#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Доказательство НЕОДНОЗНАЧНОСТИ образцов по принципу гомоморфизмов.

Принцип (двойственный к prove_unambiguous_by_homomorphism.py):
    если образец НЕОДНОЗНАЧЕН, то неоднозначны и
      (1) любой его ГОМОМОРФНЫЙ ПРООБРАЗ относительно ПЕРЕМЕННЫХ
          (каждая переменная нового образца переходит в слово над переменными
           леммы, ПУСТОЕ ДОПУСКАЕТСЯ; буквы-константы не трогаем);
      (2) любой его ГОМОМОРФНЫЙ ОБРАЗ относительно БУКВ
          (каждая буква леммы переходит в слово над буквами; морфизм может быть
           НЕинъективным — напр. B->A; переменные не трогаем).
    Операции можно композировать.

Примеры из постановки:
    неоднозначен  xAyByx  =>  неоднозначен  xAzyByzzx   (прообраз по перем., z->eps)
    неоднозначен  xAyByx  =>  неоднозначен  xAyAyx      (образ по буквам, B->A)

Соглашения проекта (как в ambiguity_heuristic.py):
    * переменные  — строчные буквы a..z (их подставляют словами над алфавитом);
    * буквы/константы — заглавные A..Z (алфавит).

КОРРЕКТНОСТЬ (почему нет ложных «неоднозначен»).
Пусть лемма P неоднозначна: есть РАЗНЫЕ подстановки sigma != tau (переменные ->
слова над буквами P) с sigma(P) = tau(P).  Мы строим КОНКРЕТНОГО кандидата в
свидетели для целевого Q и ПРОВЕРЯЕМ его подстановкой (verify):

(1) Прообраз по переменным.  phi: перем.(Q) -> слова над перем.(P) (пусто можно),
    phi(Q) = P.  Поднимаем: sigma^(q) = sigma(phi(q)),  tau^(q) = tau(phi(q)).
    Тогда sigma^(Q) = sigma(phi(Q)) = sigma(P) = tau(P) = tau^(Q) — образы равны.
    Если дополнительно sigma^ != tau^ (проверяется), то (sigma^, tau^) — свидетель
    неоднозначности Q.  Пустые образы могут «спрятать» отличие — тогда проверка
    sigma^ != tau^ просто не пройдёт, и мы НЕ объявим Q неоднозначным.

(2) Образ по буквам.  g: буквы(P) -> слова над буквами, Q = g(P).  Поднимаем:
    sigma'(v) = g(sigma(v)),  tau'(v) = g(tau(v)) (буквы Q = g(буквы P)).
    Тогда sigma'(Q) = g(sigma(P)) = g(tau(P)) = tau'(Q).  Если sigma' != tau'
    (проверяется; при НЕинъективном g отличие может схлопнуться — тогда вывод
    не делаем), то это свидетель неоднозначности Q.

(3) Композиция (1)+(2): промежуточный R = g(P), затем phi(Q) = R.

Любой найденный свидетель ОБЯЗАТЕЛЬНО проверяется подстановкой в Q (verify),
поэтому метка «НЕОДНОЗНАЧЕН» строгая, без ложных срабатываний.
"""

import argparse
import csv
import os

import ambiguity_heuristic as ah


# ---------------------------------------------------------------------------
# базовые операции над образцом (как в ambiguity_heuristic.py)
# ---------------------------------------------------------------------------
def variables(pattern):
    """Множество переменных (строчные буквы)."""
    return set(c for c in pattern if c.islower())


def letters(pattern):
    """Множество букв-констант (заглавные)."""
    return set(c for c in pattern if c.isupper())


def substitute(pattern, assign):
    """Слово: переменная -> значение (по умолчанию ''), буква -> сама буква."""
    return ah.substitute(pattern, assign)


# ---------------------------------------------------------------------------
# свидетель неоднозначности леммы P: пара словарей (sigma, tau) или None
# ---------------------------------------------------------------------------
def lemma_witness(P, binary_maxlen=4):
    """Получить (sigma, tau) — свидетель неоднозначности P из эвристики.

    Каскад тот же, что в ambiguity_heuristic.analyse: унарный -> плавные
    границы -> бинарный. Бинарный перебор ограничен binary_maxlen (он же
    защищает от взрыва по памяти на длинных образцах). Возвращает (sigma, tau)
    или None, если свидетель в пределах поиска не найден.
    """
    w = ah.unary_criterion(P)
    if w is None:
        w = ah.smooth_boundary_witness(P)
    if w is None:
        try:
            w = ah.binary_witness(P, maxlen=binary_maxlen)
        except (MemoryError, OverflowError):
            w = None
    if w is None:
        return None
    return _checked(P, w["sigma"], w["tau"])


def _checked(P, sigma, tau):
    """Вернуть (sigma, tau), если это настоящий свидетель неоднозначности P."""
    if sigma == tau or substitute(P, sigma) != substitute(P, tau):
        return None
    return sigma, tau


def parse_witness(cell):
    """Разобрать строку 'sigma={x=A, y=AA} | tau={x=AA, y=A}' -> (sigma, tau).

    Значение 'eps' трактуется как пустое слово. Возвращает None при сбое.
    """
    def parse_assign(text):
        text = text.strip()
        i, j = text.find("{"), text.rfind("}")
        if i < 0 or j < 0:
            return None
        body = text[i + 1:j].strip()
        out = {}
        if body:
            for part in body.split(","):
                if "=" not in part:
                    return None
                k, v = part.split("=", 1)
                v = v.strip()
                out[k.strip()] = "" if v == "eps" else v
        return out

    if not cell or "|" not in cell:
        return None
    left, right = cell.split("|", 1)
    sigma, tau = parse_assign(left), parse_assign(right)
    if sigma is None or tau is None:
        return None
    return sigma, tau


# ---------------------------------------------------------------------------
# (1) прообраз по ПЕРЕМЕННЫМ:  phi(Q) = P  (phi: перем.Q -> слова над перем.P)
# ---------------------------------------------------------------------------
def var_preimage_match(Q, P):
    """Найти phi с phi(Q)=P (буквы совпадают позиционно), ПУСТОЕ допускается.

    Каждая переменная Q «съедает» блок переменных P (длиной >= 0), одинаковый
    при всех её вхождениях. Буквы Q должны совпадать с буквами P позиционно.
    """
    assign = {}

    def bt(i, j):
        if i == len(Q):
            return j == len(P)
        ch = Q[i]
        if ch.isupper():                       # буква — точное совпадение
            return j < len(P) and P[j] == ch and bt(i + 1, j + 1)
        if ch in assign:                       # переменная уже привязана
            b = assign[ch]
            return P[j:j + len(b)] == b and bt(i + 1, j + len(b))
        # новая переменная: блоки переменных P длиной L >= 0 (0 => пусто)
        for L in range(0, len(P) - j + 1):
            block = P[j:j + L]
            if L > 0 and block[-1].isupper():  # блок не может содержать букв
                break
            assign[ch] = block
            if bt(i + 1, j + L):
                return True
            del assign[ch]
        return False

    return dict(assign) if bt(0, 0) else None


def lift_var_preimage(sigma, phi):
    """sigma^(q) = sigma(phi(q)): подставить sigma в слово phi(q) над перем.P."""
    return {q: "".join(sigma.get(v, "") for v in word) for q, word in phi.items()}


# ---------------------------------------------------------------------------
# (2) образ по БУКВАМ:  g(P) = Q  (g: буквы P -> непустые слова над буквами)
# ---------------------------------------------------------------------------
def letter_image_match(P, Q):
    """Найти g с g(P)=Q (переменные совпадают позиционно). g может быть НЕинъект.

    Каждая буква P «съедает» непустой блок букв Q, одинаковый при всех вхождениях;
    разные буквы P МОГУТ давать одинаковые блоки (неинъективность допустима).
    """
    assign = {}

    def bt(i, j):
        if i == len(P):
            return j == len(Q)
        ch = P[i]
        if ch.islower():                       # переменная — точное совпадение
            return j < len(Q) and Q[j] == ch and bt(i + 1, j + 1)
        if ch in assign:
            b = assign[ch]
            return Q[j:j + len(b)] == b and bt(i + 1, j + len(b))
        for L in range(1, len(Q) - j + 1):     # буква -> непустой блок букв Q
            block = Q[j:j + L]
            if block[-1].islower():            # блок не может содержать перем.
                break
            assign[ch] = block
            if bt(i + 1, j + L):
                return True
            del assign[ch]
        return False

    return dict(assign) if bt(0, 0) else None


def lift_letter_image(sigma, g):
    """sigma'(v) = g(sigma(v)): применить буквенный морфизм g к каждому слову."""
    return {v: "".join(g.get(c, c) for c in word) for v, word in sigma.items()}


# ---------------------------------------------------------------------------
# проверка кандидата в свидетели на целевом образце Q
# ---------------------------------------------------------------------------
def valid_witness(Q, sigma, tau):
    """(sigma, tau) — настоящий свидетель неоднозначности Q?"""
    return sigma != tau and substitute(Q, sigma) == substitute(Q, tau)


def split_by_letters(s):
    """Разбить образец на чередование (var-блок, буква, var-блок, буква, ...)."""
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


def enumerate_letter_images(P, Q):
    """Кандидат в промежуточный R = g(P): переменные от P, буквы от Q.

    (g не трогает переменные => R имеет переменные P; phi не трогает буквы =>
     R имеет буквы Q.)
    """
    pseg = split_by_letters(P)
    qseg = split_by_letters(Q)
    if len(pseg) != len(qseg):
        return
    out = [pseg[k] if k % 2 == 0 else qseg[k] for k in range(len(pseg))]
    yield "".join(out)


# ---------------------------------------------------------------------------
# вывод неоднозначности целевого образца Q из неоднозначной леммы P
# ---------------------------------------------------------------------------
def derive(P, Q, witP):
    """Вывести неоднозначность Q из неоднозначной леммы P со свидетелем witP.

    witP = (sigma, tau). Возвращает словарь-свидетель {strategy, phi, g, ...}
    с УЖЕ ПРОВЕРЕННЫМ свидетелем на Q, либо None.
    """
    sigma, tau = witP

    if Q == P:
        return {"strategy": "тривиально", "phi": None, "g": None,
                "sigma": sigma, "tau": tau}

    # (1) чистый прообраз по переменным: phi(Q) = P
    if [c for c in Q if c.isupper()] == [c for c in P if c.isupper()]:
        phi = var_preimage_match(Q, P)
        if phi is not None:
            s2, t2 = lift_var_preimage(sigma, phi), lift_var_preimage(tau, phi)
            if valid_witness(Q, s2, t2):
                return {"strategy": "прообраз-перем", "phi": phi, "g": None,
                        "sigma": s2, "tau": t2}

    # (2) чистый образ по буквам: g(P) = Q
    if [c for c in P if c.islower()] == [c for c in Q if c.islower()]:
        g = letter_image_match(P, Q)
        if g is not None:
            s2, t2 = lift_letter_image(sigma, g), lift_letter_image(tau, g)
            if valid_witness(Q, s2, t2):
                return {"strategy": "образ-букв", "phi": None, "g": g,
                        "sigma": s2, "tau": t2}

    # (3) композиция: R = g(P), затем phi(Q) = R
    for R in enumerate_letter_images(P, Q):
        g = letter_image_match(P, R)
        if g is None:
            continue
        phi = var_preimage_match(Q, R)
        if phi is None:
            continue
        sR, tR = lift_letter_image(sigma, g), lift_letter_image(tau, g)
        s2, t2 = lift_var_preimage(sR, phi), lift_var_preimage(tR, phi)
        if valid_witness(Q, s2, t2):
            return {"strategy": "композиция", "phi": phi, "g": g,
                    "intermediate": R, "sigma": s2, "tau": t2}
    return None


# ---------------------------------------------------------------------------
# поиск по корпусу лемм
# ---------------------------------------------------------------------------
def prove(Q, lemmas):
    """Найти лемму, из которой выводится неоднозначность Q. (P, witness) или (None,None)."""
    for P, witP in lemmas:
        w = derive(P, Q, witP)
        if w is not None:
            return P, w
    return None, None


def fmt_morphism(m):
    if not m:
        return ""
    return "{" + ", ".join("%s->%s" % (k, (v or "eps"))
                           for k, v in sorted(m.items())) + "}"


def fmt_assign(assign):
    return "{" + ", ".join("%s=%s" % (k, (v or "eps"))
                           for k, v in sorted(assign.items())) + "}"


def fmt_witness(P, w):
    parts = ["лемма=%s" % P, "способ=%s" % w["strategy"]]
    if w.get("phi"):
        parts.append("phi=%s" % fmt_morphism(w["phi"]))
    if w.get("g"):
        parts.append("g=%s" % fmt_morphism(w["g"]))
    if w.get("intermediate"):
        parts.append("R=%s" % w["intermediate"])
    parts.append("sigma=%s|tau=%s" % (fmt_assign(w["sigma"]), fmt_assign(w["tau"])))
    return "; ".join(parts)


# ---------------------------------------------------------------------------
# ввод/вывод
# ---------------------------------------------------------------------------
def read_ambiguous_lemmas(*paths):
    """Собрать НЕОДНОЗНАЧНЫЕ образцы из CSV (колонки pattern[,verdict]).

    Берём строку, если verdict содержит 'НЕОДНОЗНАЧЕН', либо если колонки
    verdict нет вовсе (файл считается списком уже-неоднозначных образцов).
    Для каждого образца считаем свидетеля эвристикой; без свидетеля — пропуск.
    """
    seen, out = set(), []
    for path in paths:
        if not path or not os.path.exists(path):
            continue
        with open(path, newline="", encoding="utf-8") as f:
            r = csv.DictReader(f)
            cols = r.fieldnames or []
            has_verdict = "verdict" in cols
            has_witness = "witness" in cols
            for row in r:
                pat = (row.get("pattern") or "").strip()
                if not pat or pat in seen:
                    continue
                if has_verdict:
                    verdict = (row.get("verdict") or "").strip()
                    if "НЕОДНОЗНАЧЕН" not in verdict:
                        continue
                # 1) готовый свидетель из CSV (быстро, без пересчёта)
                wit = None
                if has_witness:
                    parsed = parse_witness(row.get("witness") or "")
                    if parsed is not None:
                        wit = _checked(pat, *parsed)
                # 2) иначе считаем эвристикой (бинарный перебор ограничен)
                if wit is None:
                    wit = lemma_witness(pat)
                if wit is None:
                    continue
                seen.add(pat)
                out.append((pat, wit))
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

    base = "xAyByx"
    witP = lemma_witness(base)
    status = witP is not None
    ok &= status
    print("[%s] лемма %s неоднозначна, свидетель: %s"
          % ("OK" if status else "FAIL", base,
             "%s | %s" % (fmt_assign(witP[0]), fmt_assign(witP[1])) if witP else "нет"))

    # прообраз по переменным: xAyByx => xAzyByzzx (z -> eps)
    Q = "xAzyByzzx"
    w = derive(base, Q, witP)
    status = w is not None and w["strategy"] == "прообраз-перем"
    ok &= status
    print("[%s] %s => %s : %s"
          % ("OK" if status else "FAIL", base, Q, fmt_witness(base, w) if w else "нет"))

    # образ по буквам (НЕинъективный): xAyByx => xAyAyx (B -> A)
    Q = "xAyAyx"
    w = derive(base, Q, witP)
    status = w is not None and w["strategy"] == "образ-букв"
    ok &= status
    print("[%s] %s => %s : %s"
          % ("OK" if status else "FAIL", base, Q, fmt_witness(base, w) if w else "нет"))

    # переименование букв (инъективное частный случай образа): xAyByx => xCyDyx
    Q = "xCyDyx"
    w = derive(base, Q, witP)
    status = w is not None
    ok &= status
    print("[%s] %s => %s : %s"
          % ("OK" if status else "FAIL", base, Q, fmt_witness(base, w) if w else "нет"))

    # композиция: добавить переменную (z->eps) И склеить буквы (B->A): xAzyAyzx
    Q = "xAzyAyzx"
    w = derive(base, Q, witP)
    status = w is not None
    ok &= status
    print("[%s] %s => %s : %s"
          % ("OK" if status else "FAIL", base, Q, fmt_witness(base, w) if w else "нет"))

    # ЗАЩИТА ОТ ЛОЖНОГО: однозначный образец НЕ должен выводиться.
    # xAyxBy однозначен; из неоднозначной леммы xAyByx он не выводим.
    Q = "xAyxBy"
    w = derive(base, Q, witP)
    status = w is None
    ok &= status
    print("[%s] (нет вывода) %s => %s : %s"
          % ("OK" if status else "FAIL", base, Q, "нет" if w is None else fmt_witness(base, w)))

    print("=== ИТОГ:", "ВСЕ ТЕСТЫ ПРОЙДЕНЫ" if ok else "ЕСТЬ ОШИБКИ", "===")
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(
        description="Доказательство неоднозначности образцов по гомоморфизмам")
    ap.add_argument("--lemmas", nargs="*",
                    default=[os.path.join(here, "ambiguity_lemmas.csv"),
                             os.path.join(here, "ambiguity_proven.csv")],
                    help="CSV с известными неоднозначными образцами")
    ap.add_argument("-i", "--input", default=None,
                    help="CSV с целевыми образцами (первый столбец)")
    ap.add_argument("-o", "--output",
                    default=os.path.join(here, "ambiguity_proven_ambiguous_by_homomorphism.csv"))
    ap.add_argument("--selftest", action="store_true", help="прогнать самопроверку")
    ap.add_argument("targets", nargs="*", help="целевые образцы напрямую")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    lemmas = read_ambiguous_lemmas(*args.lemmas)
    print("Неоднозначных лемм со свидетелем в корпусе: %d" % len(lemmas))

    targets = args.targets or (read_patterns(args.input) if args.input else [])
    if not targets:
        print("Нет целевых образцов. Укажите их аргументами или через -i FILE.")
        print("Подсказка: запустите с --selftest для демонстрации.")
        return 0

    fields = ["pattern", "proven", "base_lemma", "strategy", "phi", "g",
              "intermediate", "sigma", "tau"]
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
                "proven": "НЕОДНОЗНАЧЕН" if proven else "не выведено",
                "base_lemma": P or "",
                "strategy": wit["strategy"] if wit else "",
                "phi": fmt_morphism(wit.get("phi")) if wit else "",
                "g": fmt_morphism(wit.get("g")) if wit else "",
                "intermediate": wit.get("intermediate", "") if wit else "",
                "sigma": fmt_assign(wit["sigma"]) if wit else "",
                "tau": fmt_assign(wit["tau"]) if wit else "",
            }
            w.writerow(row)
            f.flush()
            print("[%s] %s" % ("ОК " if proven else "-- ", Q),
                  fmt_witness(P, wit) if proven else "")

    print("\nВыведено неоднозначных: %d из %d  ->  %s"
          % (n_ok, len(targets), args.output))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
