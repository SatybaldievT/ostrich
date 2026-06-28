#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ОРКЕСТРАТОР («корпус») классификации образцов на одно/неоднозначность.

Для КАЖДОГО образца по очереди применяются ступени; на первом полученном
вердикте обработка образца ОСТАНАВЛИВАЕТСЯ:

  1. ЛЕММЫ (без решателя)
     1а. Единственная переменная во всём образце.
         Пробуем найти свидетеля неоднозначности прямым поиском; если найден —
         НЕОДНОЗНАЧЕН (проверен подстановкой). Иначе по лемме «одна переменная»:
         её значение однозначно определяется образом => ОДНОЗНАЧЕН.
     1б. Лемма из картинки (8):  x^n (A_i y)_{1<=i<=n},  все A_i различны, n>2
         => ОДНОЗНАЧЕН.  (Случай n=2 — отдельный, лемма не применяется.)

  2. ГОМОМОРФИЗМЫ (без решателя) — prove_by_homomorphism.classify:
     подъём из корпуса проверенных лемм по образам/прообразам относительно
     переменных и букв (обе стороны). Метки проверяются.

  3. БАЛАНСИРУЮЩИЕ РАЗРЕЗЫ (без решателя) — unambiguity_heuristic:
     лемма об однозначности по балансирующему разрезу xi C1 .. | xi C2 ..
     (C1 != C2). При ровно двух переменных => ОДНОЗНАЧЕН.

  4. УНАРНЫЙ + СКОЛЬЗЯЩИЕ (без решателя) — ambiguity_heuristic:
     unary_criterion и smooth_boundary_witness. Найденный свидетель проверяется
     подстановкой => НЕОДНОЗНАЧЕН.

  5. OSTRICH (базовый, без классов коммутации) — на образцах, не решённых
     эвристиками. sat => НЕОДНОЗНАЧЕН (свидетель из модели проверяется),
     unsat => ОДНОЗНАЧЕН (в пределах длины перебора решателя),
     unknown/timeout => не определено.

Запуск:
    python corpus_pipeline.py                # на «оставшихся» образцах бенчмарка
    python corpus_pipeline.py -i FILE.csv -o OUT.csv
    python corpus_pipeline.py xAyByx xAyxBy  # конкретные образцы
    python corpus_pipeline.py --no-ostrich   # только эвристики (ступени 1–4)
    python corpus_pipeline.py --selftest
"""

import argparse
import csv
import itertools
import os

import ambiguity_heuristic as ah
import prove_by_homomorphism as H
import unambiguity_heuristic as uh

HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# базовое
# ---------------------------------------------------------------------------
def variables(pattern):
    return sorted(set(c for c in pattern if c.islower()))


def constants(pattern):
    return sorted(set(c for c in pattern if c.isupper()))


def substitute(pattern, assign):
    return ah.substitute(pattern, assign)


def fmt_assign(assign):
    return "{" + ", ".join("%s=%s" % (k, (v or "eps"))
                           for k, v in sorted(assign.items())) + "}"


# ---------------------------------------------------------------------------
# Ступень 1а. Единственная переменная во всём образце
# ---------------------------------------------------------------------------
def single_variable_stage(pattern, search_len=4):
    """Если переменная ровно одна — вернуть вердикт, иначе None.

    Сначала ЧЕСТНО пытаемся найти свидетеля sigma!=tau с равными образами
    (перебор значений единственной переменной над алфавитом образца). Для одной
    переменной такого свидетеля не существует (её значение восстанавливается из
    образа), поэтому поиск служит подтверждением, после чего выносим ОДНОЗНАЧЕН.
    """
    vs = variables(pattern)
    if len(vs) != 1:
        return None
    v = vs[0]
    alphabet = constants(pattern) or ["A"]
    words = ["".join(t) for n in range(1, search_len + 1)
             for t in itertools.product(alphabet, repeat=n)]
    for u1, u2 in itertools.combinations(words, 2):
        if substitute(pattern, {v: u1}) == substitute(pattern, {v: u2}):
            return {
                "verdict": "НЕОДНОЗНАЧЕН",
                "stage": "лемма:одна-перем",
                "detail": "свидетель sigma=%s|tau=%s"
                          % (fmt_assign({v: u1}), fmt_assign({v: u2})),
                "sigma": {v: u1}, "tau": {v: u2},
            }
    return {
        "verdict": "ОДНОЗНАЧЕН",
        "stage": "лемма:одна-перем",
        "detail": "одна переменная %s: значение определяется образом" % v,
    }


# ---------------------------------------------------------------------------
# Ступень 1б. Лемма из картинки:  x^n (A_i y),  A_i различны,  n > 2
# ---------------------------------------------------------------------------
def picture_lemma_stage(pattern):
    """Распознать форму x^n A_1 y A_2 y ... A_n y (A_i различны, n>2) -> вердикт."""
    if not pattern or not pattern[0].islower():
        return None
    xvar = pattern[0]
    i = 0
    while i < len(pattern) and pattern[i] == xvar:
        i += 1
    n = i                                 # длина ведущего блока x^n
    if n <= 2:
        return None
    rest = pattern[i:]
    if len(rest) != 2 * n:                # ровно n блоков (буква + y)
        return None
    yset = set(c for c in rest if c.islower())
    if len(yset) != 1:
        return None
    yvar = next(iter(yset))
    if yvar == xvar:
        return None
    consts = []
    for k in range(n):
        c, yy = rest[2 * k], rest[2 * k + 1]
        if not c.isupper() or yy != yvar:
            return None
        consts.append(c)
    if len(set(consts)) != n:            # все A_i различны
        return None
    return {
        "verdict": "ОДНОЗНАЧЕН",
        "stage": "лемма:картинка(8)",
        "detail": "x^%d (A_i y), A_i различны (%s), n>2" % (n, "".join(consts)),
    }


# ---------------------------------------------------------------------------
# Ступень 2. Гомоморфизмы
# ---------------------------------------------------------------------------
def homomorphism_stage(pattern, unamb_lemmas, amb_lemmas):
    r = H.classify(pattern, unamb_lemmas, amb_lemmas)
    v = r["verdict"]
    if v in ("ОДНОЗНАЧЕН", "НЕОДНОЗНАЧЕН"):
        base = r["amb_lemma"] or r["unamb_lemma"]
        strat = r["amb_strategy"] or r["unamb_strategy"]
        return {"verdict": v, "stage": "гомоморфизм",
                "detail": "<= %s (%s)" % (base, strat)}
    if v == "КОНФЛИКТ(!)":
        return {"verdict": "КОНФЛИКТ(!)", "stage": "гомоморфизм",
                "detail": "обе стороны вывелись — проверить корпус"}
    return None


# ---------------------------------------------------------------------------
# Ступень 3. Балансирующие разрезы (однозначность)
# ---------------------------------------------------------------------------
def balancing_stage(pattern):
    w = uh.unambiguity_lemma(pattern)
    if w is None or not w["overall"]:    # overall => ровно две переменные
        return None
    return {"verdict": "ОДНОЗНАЧЕН", "stage": "балансир.разрез",
            "detail": "%s: %s|%s (%s!=%s)"
                      % (w["side"], w["w1"], w["w2"], w["c1"], w["c2"])}


# ---------------------------------------------------------------------------
# Ступень 4. Унарный + скользящие границы (неоднозначность, без решателя)
# ---------------------------------------------------------------------------
def heuristic_ambiguity_stage(pattern):
    w = ah.unary_criterion(pattern)
    crit = "унарный"
    if w is None:
        w = ah.smooth_boundary_witness(pattern)
        crit = "скользящие"
    if w is None:
        return None
    sigma, tau = w["sigma"], w["tau"]
    if sigma == tau or substitute(pattern, sigma) != substitute(pattern, tau):
        return None                      # свидетель не прошёл проверку
    return {"verdict": "НЕОДНОЗНАЧЕН", "stage": "эвристика:%s" % crit,
            "detail": "sigma=%s|tau=%s" % (fmt_assign(sigma), fmt_assign(tau)),
            "sigma": sigma, "tau": tau}


# ---------------------------------------------------------------------------
# Ступень 5. Ostrich (базовый)
# ---------------------------------------------------------------------------
class OstrichStage:
    """Ленивая тёплая сессия базового Ostrich; пересоздаётся каждые recycle задач."""

    def __init__(self, timeout_ms=20000, recycle=25, max_len=20):
        self.timeout_ms = timeout_ms
        self.recycle = recycle
        self.max_len = max_len
        self._mod = None
        self._runner = None
        self._session = None
        self._since = 0
        self.available = None            # None=не пробовали, True/False=итог
        self.error = ""

    def _ensure(self):
        if self.available is False:
            return False
        try:
            if self._mod is None:
                import ostrich_session as oss
                import ostrich_runner as runner
                self._mod, self._runner = oss, runner
                runner.find_jar()        # бросит, если jar не собран
            if self._session is None or not self._session.alive() \
                    or (self.recycle and self._since >= self.recycle):
                if self._session is not None:
                    self._session.close()
                self._session = self._mod.OstrichSession(
                    flags=self._runner.BASELINE_FLAGS,   # БАЗОВЫЙ Ostrich
                    timeout_ms=self.timeout_ms)
                self._since = 0
            self.available = True
            return True
        except Exception as e:            # jar не найден / java нет / запуск упал
            self.available = False
            self.error = str(e).splitlines()[0] if str(e) else type(e).__name__
            return False

    def run(self, pattern):
        if not self._ensure():
            return {"verdict": "не определено", "stage": "ostrich",
                    "detail": "Ostrich недоступен: %s" % self.error}
        r = self._mod.solve_pattern(self._session, pattern,
                                    mode="base", max_len=self.max_len)
        self._since += 1
        status = r["status"]
        if status == "sat":
            ok, note = _verify_counter(pattern, r.get("counter_example", ""))
            return {"verdict": "НЕОДНОЗНАЧЕН", "stage": "ostrich",
                    "detail": "sat; %s" % note, "witness_valid": ok}
        if status == "unsat":
            return {"verdict": "ОДНОЗНАЧЕН", "stage": "ostrich",
                    "detail": "unsat (в пределах длины %d)" % self.max_len}
        return {"verdict": "не определено", "stage": "ostrich",
                "detail": "status=%s (time=%.1fs)" % (status, r.get("time", 0.0))}

    def close(self):
        if self._session is not None:
            self._session.close()


def _verify_counter(pattern, counter_example):
    """Проверить свидетеля из модели: '[a=..]!=[a=..]' -> слова равны, наборы разные."""
    import check_uniqueness as cu
    a1, a2 = cu.parse_counter_example(counter_example or "")
    if not a1 or not a2:
        return False, "свидетель не разобран"
    w1, w2 = substitute(pattern, a1), substitute(pattern, a2)
    ok = (w1 == w2) and (a1 != a2)
    return ok, ("свидетель верен" if ok else "СВИДЕТЕЛЬ НЕ ПРОШЁЛ ПРОВЕРКУ")


# ---------------------------------------------------------------------------
# конвейер
# ---------------------------------------------------------------------------
def classify_pattern(pattern, unamb_lemmas, amb_lemmas, ostrich=None):
    """Прогнать образец по ступеням; вернуть строку результата (dict)."""
    stages = [
        lambda p: single_variable_stage(p),
        lambda p: picture_lemma_stage(p),
        lambda p: homomorphism_stage(p, unamb_lemmas, amb_lemmas),
        lambda p: balancing_stage(p),
        lambda p: heuristic_ambiguity_stage(p),
    ]
    for st in stages:
        r = st(pattern)
        if r is not None:
            r["pattern"] = pattern
            return r
    if ostrich is not None:
        r = ostrich.run(pattern)
        r["pattern"] = pattern
        return r
    return {"pattern": pattern, "verdict": "не выведено",
            "stage": "—", "detail": "эвристики не дали вердикта (Ostrich отключён)"}


# ---------------------------------------------------------------------------
# ввод/вывод
# ---------------------------------------------------------------------------
def read_patterns(path):
    out = []
    with open(path, newline="", encoding="utf-8") as f:
        r = csv.reader(f)
        next(r, None)
        for row in r:
            if row and row[0].strip():
                out.append(row[0].strip())
    return out


def load_ground_truth(path):
    """{pattern -> '+'/'-'/'-?'} из patterns_ambiguity.csv (или {} если нет)."""
    if not os.path.exists(path):
        return {}
    out = {}
    with open(path, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            p = (row.get("pattern") or "").strip()
            a = (row.get("ambiguity") or "").strip()
            if p:
                out[p] = a
    return out


def gt_consistent(verdict, gt):
    """Согласуется ли наш вердикт с эталонной меткой ambiguity (+ / - / -?)."""
    if not gt:
        return None
    if verdict == "НЕОДНОЗНАЧЕН":
        return gt == "+"
    if verdict == "ОДНОЗНАЧЕН":
        return gt in ("-", "-?")
    return None


# ---------------------------------------------------------------------------
# самопроверка
# ---------------------------------------------------------------------------
def selftest():
    print("=== САМОПРОВЕРКА КОНВЕЙЕРА (ступени 1–4, без Ostrich) ===")
    unamb = H.read_unambiguous_lemmas(os.path.join(HERE, "ambiguity_lemmas.csv"))
    amb = H.read_ambiguous_lemmas(os.path.join(HERE, "ambiguity_lemmas.csv"),
                                  os.path.join(HERE, "ambiguity_proven.csv"))
    cases = [
        ("xAxBx",     "ОДНОЗНАЧЕН",  "лемма:одна-перем"),   # одна переменная
        ("xxxAyByCy", "ОДНОЗНАЧЕН",  "лемма:картинка(8)"),  # x^3 (Ay Cy ...) n=3
        ("xyAyxyBy",  "ОДНОЗНАЧЕН",  "гомоморфизм"),        # образ-перем из xAyxBy
        ("xAyByx",    "НЕОДНОЗНАЧЕН", None),                # унарный/эвристика
        ("xAyxBy",    "ОДНОЗНАЧЕН",  None),                 # балансир.разрез/гомоморфизм
    ]
    ok = True
    for p, exp_v, exp_s in cases:
        r = classify_pattern(p, unamb, amb, ostrich=None)
        good = r["verdict"] == exp_v and (exp_s is None or r["stage"] == exp_s)
        ok &= good
        print("[%s] %-11s -> %-13s [%s] %s"
              % ("OK" if good else "FAIL", p, r["verdict"], r["stage"], r["detail"]))
    print("=== ИТОГ:", "ВСЕ ТЕСТЫ ПРОЙДЕНЫ" if ok else "ЕСТЬ ОШИБКИ", "===")
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Оркестратор классификации образцов по ступеням")
    ap.add_argument("-i", "--input",
                    default=os.path.join(HERE, "patterns_ambiguity_col_missing_from_proven_or_lemmas.csv"),
                    help="CSV с целевыми образцами (первый столбец)")
    ap.add_argument("-o", "--output", default=os.path.join(HERE, "corpus_pipeline_results.csv"))
    ap.add_argument("--unamb-lemmas", nargs="*",
                    default=[os.path.join(HERE, "ambiguity_lemmas.csv")])
    ap.add_argument("--amb-lemmas", nargs="*",
                    default=[os.path.join(HERE, "ambiguity_lemmas.csv"),
                             os.path.join(HERE, "ambiguity_proven.csv")])
    ap.add_argument("--no-ostrich", action="store_true", help="не запускать ступень 5 (Ostrich)")
    ap.add_argument("--ostrich-timeout", type=int, default=20, help="таймаут Ostrich на образец, с")
    ap.add_argument("--max-len", type=int, default=20, help="граница длины переменных в Ostrich")
    ap.add_argument("--gt", default=os.path.join(HERE, "patterns_ambiguity.csv"),
                    help="CSV с эталонной колонкой ambiguity для сверки")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("targets", nargs="*", help="образцы напрямую")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    unamb = H.read_unambiguous_lemmas(*args.unamb_lemmas)
    amb = H.read_ambiguous_lemmas(*args.amb_lemmas)
    print("Корпус лемм: однозначных %d, неоднозначных со свидетелем %d"
          % (len(unamb), len(amb)))

    targets = args.targets or read_patterns(args.input)
    gt = load_ground_truth(args.gt)
    ostrich = None if args.no_ostrich else OstrichStage(
        timeout_ms=args.ostrich_timeout * 1000, max_len=args.max_len)

    fields = ["pattern", "verdict", "stage", "detail", "gt", "gt_ok"]
    from collections import Counter
    by_stage = Counter()
    by_verdict = Counter()
    conflicts, gt_bad = [], []

    with open(args.output, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for idx, p in enumerate(targets, 1):
            r = classify_pattern(p, unamb, amb, ostrich=ostrich)
            g = gt.get(p, "")
            cons = gt_consistent(r["verdict"], g)
            row = {"pattern": p, "verdict": r["verdict"], "stage": r["stage"],
                   "detail": r["detail"], "gt": g,
                   "gt_ok": "" if cons is None else ("ok" if cons else "MISMATCH")}
            w.writerow(row)
            f.flush()
            by_stage[r["stage"]] += 1
            by_verdict[r["verdict"]] += 1
            if r["verdict"] == "КОНФЛИКТ(!)":
                conflicts.append(p)
            if cons is False:
                gt_bad.append((p, r["verdict"], g, r["stage"]))
            print("[%d/%d] %-13s %-13s %-18s %s"
                  % (idx, len(targets), p, r["verdict"], r["stage"], r["detail"]),
                  flush=True)

    if ostrich is not None:
        ostrich.close()

    print("\n===== ИТОГ =====")
    print("  всего образцов: %d" % len(targets))
    for v, c in by_verdict.most_common():
        print("    %-14s %d" % (v, c))
    print("  по ступеням:")
    for s, c in by_stage.most_common():
        print("    %-20s %d" % (s, c))
    if gt:
        print("  сверка с эталоном: расхождений %d" % len(gt_bad))
        for p, v, g, s in gt_bad:
            print("    !!! %-12s наш=%s эталон=%s [%s]" % (p, v, g, s))
    if conflicts:
        print("  КОНФЛИКТЫ (ОШИБКА!): %d -> %s" % (len(conflicts), ", ".join(conflicts)))
    print("\nЗаписано -> %s" % args.output)
    return 1 if conflicts else 0


if __name__ == "__main__":
    raise SystemExit(main())
