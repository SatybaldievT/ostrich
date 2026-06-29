#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Доказательство ОДНОЗНАЧНОСТИ образцов по принципу гомоморфизмов.

Принцип (даётся как лемма):
    если образец ОДНОЗНАЧЕН, то однозначны и
      (1) любой его ГОМОМОРФНЫЙ ОБРАЗ относительно ПЕРЕМЕННЫХ
          (каждая переменная заменяется непустым словом над переменными;
           буквы-константы не трогаем);
      (2) любой его ГОМОМОРФНЫЙ ПРООБРАЗ относительно БУКВ
          (буквы образца получаются ИНЪЕКТИВНЫМ морфизмом из букв нового
           образца; переменные не трогаем).
    Операции можно композировать.

Пример из постановки:
    однозначен  xAyxBy   =>   однозначен  xyAyxyBy
    (морфизм по переменным  phi: x -> xy,  y -> y).

Соглашения проекта (как в ambiguity_heuristic.py):
    * переменные  — строчные буквы a..z (их подставляют словами);
    * буквы/константы — заглавные A..Z (фиксированный алфавит).

КОРРЕКТНОСТЬ (почему нет ложных «однозначен»).
Пусть P однозначен. Однозначность P означает: нет двух РАЗНЫХ подстановок
sigma != tau (переменные -> слова над буквами) с sigma(P) = tau(P).

(1) Образ по переменным.  Q = phi(P), где phi: перем. -> слова над перем.
    Если sigma(Q) = tau(Q), то (sigma∘phi)(P) = (tau∘phi)(P), значит по
    однозначности P:  sigma(phi(v)) = tau(phi(v)) для каждой переменной v
    образца P  (это «блочные равенства»).  Чтобы отсюда следовало sigma = tau
    (равенство на КАЖДОЙ переменной Q), достаточно, чтобы блочные равенства
    «разрешались»: см. determinacy_closure() — она формализует сокращение в
    свободной полугруппе (если в блоке не определена ровно одна переменная,
    её значения у sigma и tau вынужденно совпадают). Если так определяются
    ВСЕ переменные Q — переход корректен.

(2) Прообраз по буквам.  psi: буквы(Q) -> слова над буквами(P), psi(Q) = P,
    psi ИНЪЕКТИВЕН как морфизм (код, проверка Сардинаса–Паттерсона).
    Если sigma(Q) = tau(Q), то psi(sigma(Q)) = psi(tau(Q)); это равно
    sigma'(P) = tau'(P) c sigma'(v) = psi(sigma(v)).  По однозначности P:
    sigma'(v) = tau'(v), т.е. psi(sigma(v)) = psi(tau(v)); инъективность psi
    даёт sigma(v) = tau(v).  Значит Q однозначен.

Каждый найденный вывод дополнительно ПРОВЕРЯЕТСЯ: морфизм реально переводит
лемму в целевой образец (см. verify_derivation()).
"""

import argparse
import csv
import os


# ---------------------------------------------------------------------------
# базовые операции над образцом
# ---------------------------------------------------------------------------
def variables(pattern):
    """Множество переменных (строчные буквы)."""
    return set(c for c in pattern if c.islower())


def letters(pattern):
    """Множество букв-констант (заглавные)."""
    return set(c for c in pattern if c.isupper())


def apply_var_morphism(pattern, phi):
    """phi: переменная -> слово над переменными; буквы остаются собой."""
    return "".join(phi[c] if c.islower() else c for c in pattern)


def apply_letter_morphism(pattern, psi):
    """psi: буква -> слово над буквами; переменные остаются собой."""
    return "".join(psi[c] if c.isupper() else c for c in pattern)


# ---------------------------------------------------------------------------
# (1) поиск морфизма по ПЕРЕМЕННЫМ:  phi(P) = Q
# ---------------------------------------------------------------------------
def var_image_match(P, Q):
    """Найти phi (перем.P -> непустое слово над перем.) с phi(P)=Q или None.

    Буквы-константы должны совпадать позиционно; каждая переменная P
    «съедает» непустой блок переменных Q, одинаковый при всех её вхождениях.
    """
    assign = {}

    def bt(i, j):
        if i == len(P):
            return j == len(Q)
        ch = P[i]
        if ch.isupper():                       # константа — точное совпадение
            return j < len(Q) and Q[j] == ch and bt(i + 1, j + 1)
        if ch in assign:                       # переменная уже привязана
            b = assign[ch]
            return Q[j:j + len(b)] == b and bt(i + 1, j + len(b))
        # новая переменная: пробуем блоки переменных Q длиной >= 1
        for L in range(1, len(Q) - j + 1):
            block = Q[j:j + L]
            if block[-1].isupper():            # блок не может содержать букв
                break
            assign[ch] = block
            if bt(i + 1, j + L):
                return True
            del assign[ch]
        return False

    return dict(assign) if bt(0, 0) else None


def determinacy_closure(phi, Qvars):
    """Можно ли из блочных равенств вывести равенство на КАЖДОЙ перем. Q.

    Замыкание-сокращение: блок (= одно из значений phi(v)), в котором ровно
    одна ещё-неопределённая переменная (возможно с повторами), вынуждает
    равенство значений sigma/tau на ней (сокращение слева/справа в свободной
    полугруппе; кратные вхождения дают равные длины => равенство).
    Возвращает True, если так определяются все переменные Q.
    """
    blocks = list(phi.values())
    determined = set()
    changed = True
    while changed:
        changed = False
        for b in blocks:
            undet = set(c for c in b if c.islower() and c not in determined)
            if len(undet) == 1:
                determined |= undet
                changed = True
    return Qvars <= determined


# ---------------------------------------------------------------------------
# (2) поиск морфизма по БУКВАМ:  psi(Q) = P  (Q — прообраз леммы P)
# ---------------------------------------------------------------------------
def letter_preimage_match(P, Q):
    """Найти psi (буквы Q -> непустое слово над буквами P) с psi(Q)=P или None.

    Переменные фиксированы и должны совпадать позиционно; каждая буква Q
    «съедает» непустой блок букв P, одинаковый при всех вхождениях.
    """
    assign = {}

    def bt(i, j):
        if i == len(Q):
            return j == len(P)
        ch = Q[i]
        if ch.islower():                       # переменная — точное совпадение
            return j < len(P) and P[j] == ch and bt(i + 1, j + 1)
        if ch in assign:
            b = assign[ch]
            return P[j:j + len(b)] == b and bt(i + 1, j + len(b))
        for L in range(1, len(P) - j + 1):
            block = P[j:j + L]
            if block[-1].islower():            # блок не может содержать перем.
                break
            assign[ch] = block
            if bt(i + 1, j + L):
                return True
            del assign[ch]
        return False

    return dict(assign) if bt(0, 0) else None


def is_code(words):
    """Инъективен ли морфизм с такими образами (алгоритм Сардинаса–Паттерсона)."""
    C = set(w for w in words if w)
    if len(C) < len(set(words)):               # повтор слова -> не код по перем.
        pass                                   # одинаковые значения допустимы
    if not C:
        return True

    def succ(S):
        out = set()
        for w in C:
            for s in S:
                if w != s and w.startswith(s):
                    out.add(w[len(s):])
                if w != s and s.startswith(w):
                    out.add(s[len(w):])
        return out

    S = set()
    for a in C:
        for b in C:
            if a != b and b.startswith(a):
                S.add(b[len(a):])
    seen = set()
    while S and frozenset(S) not in seen:
        if C & S:                              # дозовый суффикс = кодовое слово
            return False
        seen.add(frozenset(S))
        S = succ(S)
    return True


def is_injective_letter_morphism(psi):
    """psi инъективен <=> различные буквы дают различные образы И они код."""
    vals = list(psi.values())
    if len(set(vals)) != len(vals):            # две буквы -> одно слово: не инъект.
        return False
    return is_code(vals)


# ---------------------------------------------------------------------------
# вывод однозначности целевого образца из леммы
# ---------------------------------------------------------------------------
def verify_derivation(P, Q, phi=None, psi=None):
    """Проверить, что (phi/psi) действительно переводит лемму P в образец Q.

    Композиция: сначала образ по переменным R = phi(P), затем Q — прообраз R
    по буквам, т.е. psi(Q) = R.
    """
    R = apply_var_morphism(P, phi) if phi else P
    if psi:
        return apply_letter_morphism(Q, psi) == R
    return Q == R


def derive(P, Q):
    """Попытаться вывести однозначность Q из однозначной леммы P.

    Возвращает словарь-свидетель {strategy, phi, psi, ...} или None.
    Стратегии (все корректны, см. шапку файла):
      * 'тривиально'      — Q == P;
      * 'образ-перем'     — phi(P) = Q (морфизм по переменным);
      * 'прообраз-букв'   — psi(Q) = P (инъективный морфизм по буквам);
      * 'композиция'      — psi(Q) = phi(P).
    """
    if Q == P:
        return {"strategy": "тривиально", "phi": None, "psi": None}

    # (1) чистый образ по переменным
    if variables_ok(P, Q):
        phi = var_image_match(P, Q)
        if phi is not None and determinacy_closure(phi, variables(Q)):
            if verify_derivation(P, Q, phi=phi):
                return {"strategy": "образ-перем", "phi": phi, "psi": None}

    # (2) чистый прообраз по буквам
    psi = letter_preimage_match(P, Q)
    if psi is not None and is_injective_letter_morphism(psi):
        if verify_derivation(P, Q, psi=psi):
            return {"strategy": "прообраз-букв", "phi": None, "psi": psi}

    # (3) композиция: R = phi(P), psi(Q) = R.
    #     R имеет тот же «буквенный скелет», что P (phi не трогает буквы),
    #     и тот же скелет переменных, что Q (psi не трогает переменные).
    #     Перебираем образы R по переменным из P и проверяем прообраз по буквам.
    for R in enumerate_var_images(P, Q):
        phi = var_image_match(P, R)
        if phi is None or not determinacy_closure(phi, variables(R)):
            continue
        psi = letter_preimage_match(R, Q)      # psi(Q) = R
        if psi is not None and is_injective_letter_morphism(psi):
            if verify_derivation(P, Q, phi=phi, psi=psi):
                return {"strategy": "композиция", "phi": phi, "psi": psi,
                        "intermediate": R}
    return None


def variables_ok(P, Q):
    """Быстрый отсев: у образа по переменным буквы совпадают по мультимножеству."""
    return [c for c in P if c.isupper()] == [c for c in Q if c.isupper()]


def enumerate_var_images(P, Q):
    """Кандидаты в промежуточный R для композиции.

    R = phi(P): тот же буквенный скелет, что у P; число переменных между
    соседними буквами как у Q (т.к. psi по буквам не меняет переменные).
    Строим R, копируя переменные Q, но буквы беря из P.
    """
    # сегменты по буквам: P-буквы как разделители у P, Q-буквы у Q.
    # переменные R берём из Q посегментно, буквы — из P.
    Pletters = [c for c in P if c.isupper()]
    Qletters = [c for c in Q if c.isupper()]
    if len(Pletters) != len(Qletters):
        return
    # разбить P и Q на чередование (var-блок, буква, var-блок, буква, ...)
    def split_by_letters(s):
        segs, cur = [], []
        for ch in s:
            if ch.isupper():
                segs.append("".join(cur))
                segs.append(ch)
                cur = []
            else:
                cur.append(ch)
        segs.append("".join(cur))
        return segs

    pseg = split_by_letters(P)
    qseg = split_by_letters(Q)
    if len(pseg) != len(qseg):
        return
    # R: переменные-сегменты от Q, буквы от P
    out = []
    for k in range(len(pseg)):
        out.append(pseg[k] if k % 2 == 1 else qseg[k])
    yield "".join(out)


# ---------------------------------------------------------------------------
# поиск по корпусу лемм
# ---------------------------------------------------------------------------
def fmt_morphism(m):
    if not m:
        return ""
    return "{" + ", ".join("%s->%s" % (k, v) for k, v in sorted(m.items())) + "}"


def fmt_witness(P, w):
    parts = ["лемма=%s" % P, "способ=%s" % w["strategy"]]
    if w.get("phi"):
        parts.append("phi=%s" % fmt_morphism(w["phi"]))
    if w.get("psi"):
        parts.append("psi=%s" % fmt_morphism(w["psi"]))
    if w.get("intermediate"):
        parts.append("R=%s" % w["intermediate"])
    return "; ".join(parts)


def prove(Q, lemmas):
    """Найти лемму, из которой выводится однозначность Q. Вернуть (P, witness)."""
    for P in lemmas:
        w = derive(P, Q)
        if w is not None:
            return P, w
    return None, None


# ---------------------------------------------------------------------------
# ввод/вывод
# ---------------------------------------------------------------------------
def read_unambiguous_lemmas(path):
    """Прочитать ОДНОЗНАЧНЫЕ образцы из ambiguity_lemmas.csv."""
    out = []
    with open(path, newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        for row in r:
            pat = (row.get("pattern") or "").strip()
            verdict = (row.get("verdict") or "").strip()
            if pat and verdict == "ОДНОЗНАЧЕН":   # NB: подстрока в НЕОДНОЗНАЧЕН
                out.append(pat)
    return out


def read_patterns(path):
    out = []
    with open(path, newline="", encoding="utf-8") as f:
        r = csv.reader(f)
        next(r, None)
        for row in r:
            if row and row[0].strip():
                out.append(row[0].strip())
    return out


# ---------------------------------------------------------------------------
# самопроверка
# ---------------------------------------------------------------------------
def selftest():
    print("=== САМОПРОВЕРКА ===")
    ok = True

    # пример из постановки: xAyxBy => xyAyxyBy  (phi: x->xy, y->y)
    P, Q = "xAyxBy", "xyAyxyBy"
    w = derive(P, Q)
    status = w is not None and w["strategy"] == "образ-перем" \
        and w["phi"] == {"x": "xy", "y": "y"}
    ok &= status
    print("[%s] %s => %s : %s" %
          ("OK" if status else "FAIL", P, Q, fmt_witness(P, w) if w else "нет"))

    # ещё один образ по переменным: y -> yx
    P, Q = "xAyxBy", "xAyxxByx"
    w = derive(P, Q)
    status = w is not None
    ok &= status
    print("[%s] %s => %s : %s" %
          ("OK" if status else "FAIL", P, Q, fmt_witness(P, w) if w else "нет"))

    # прообраз по буквам: переименование A->C, B->D (инъективно)
    P, Q = "xAyxBy", "xCyxDy"
    w = derive(P, Q)
    status = w is not None and w["strategy"] == "прообраз-букв"
    ok &= status
    print("[%s] %s => %s : %s" %
          ("OK" if status else "FAIL", P, Q, fmt_witness(P, w) if w else "нет"))

    # НЕ должно доказываться из этой леммы: другой буквенный скелет/структура
    P, Q = "xAyxBy", "xAxBy"     # xAxBy помечен НЕОДНОЗНАЧЕН в данных
    w = derive(P, Q)
    status = w is None
    ok &= status
    print("[%s] (нет вывода) %s => %s : %s" %
          ("OK" if status else "FAIL", P, Q, "нет" if w is None else fmt_witness(P, w)))

    # ЗАЩИТА ОТ ЛОЖНОГО: x (однозначен) -> uu' (НЕоднозначен) запрещён
    #   determinacy_closure должен отвергнуть phi: x->yz
    phi = {"x": "yz"}
    status = not determinacy_closure(phi, {"y", "z"})
    ok &= status
    print("[%s] determinacy отвергает x->yz (две новые перем. в одном блоке)"
          % ("OK" if status else "FAIL"))

    print("=== ИТОГ:", "ВСЕ ТЕСТЫ ПРОЙДЕНЫ" if ok else "ЕСТЬ ОШИБКИ", "===")
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(
        description="Доказательство однозначности образцов по гомоморфизмам")
    ap.add_argument("--lemmas", default=os.path.join(here, "ambiguity_lemmas.csv"),
                    help="CSV с известными однозначными образцами (pattern,verdict,...)")
    ap.add_argument("-i", "--input", default=None,
                    help="CSV с целевыми образцами (первый столбец)")
    ap.add_argument("-o", "--output",
                    default=os.path.join(here, "ambiguity_proven_by_homomorphism.csv"))
    ap.add_argument("--selftest", action="store_true", help="прогнать самопроверку")
    ap.add_argument("targets", nargs="*", help="целевые образцы напрямую")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    lemmas = read_unambiguous_lemmas(args.lemmas)
    print("Однозначных лемм в корпусе: %d" % len(lemmas))

    targets = args.targets or (read_patterns(args.input) if args.input else [])
    if not targets:
        print("Нет целевых образцов. Укажите их аргументами или через -i FILE.")
        print("Подсказка: запустите с --selftest для демонстрации.")
        return 0

    fields = ["pattern", "proven", "base_lemma", "strategy", "phi", "psi",
              "intermediate"]
    n_ok = 0
    with open(args.output, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for Q in targets:
            P, wit = prove(Q, lemmas)
            proven = wit is not None
            n_ok += proven
            row = {
                "pattern": Q,
                "proven": "ОДНОЗНАЧЕН" if proven else "не выведено",
                "base_lemma": P or "",
                "strategy": wit["strategy"] if wit else "",
                "phi": fmt_morphism(wit.get("phi")) if wit else "",
                "psi": fmt_morphism(wit.get("psi")) if wit else "",
                "intermediate": wit.get("intermediate", "") if wit else "",
            }
            w.writerow(row)
            f.flush()
            print("[%s] %s" % ("ОК " if proven else "-- ", Q),
                  fmt_witness(P, wit) if proven else "")

    print("\nВыведено однозначных: %d из %d  ->  %s"
          % (n_ok, len(targets), args.output))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
