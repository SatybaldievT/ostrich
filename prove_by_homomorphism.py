#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Классификация образцов по принципу ГОМОМОРФИЗМОВ — обе стороны в одной программе.

Объединяет две двойственные леммы:

  ОДНОЗНАЧНОСТЬ (если P однозначен, то однозначны и ...):
    (U1) ГОМОМОРФНЫЙ ОБРАЗ по ПЕРЕМЕННЫМ — каждая переменная P переходит в
         НЕПУСТОЕ слово над переменными (буквы не трогаем);
    (U2) ГОМОМОРФНЫЙ ПРООБРАЗ по БУКВАМ — буквы P получаются ИНЪЕКТИВНЫМ
         морфизмом из букв нового образца (переменные не трогаем).
    Пример:  однозначен xAyxBy  =>  однозначен xyAyxyBy   (phi: x->xy, y->y).

  НЕОДНОЗНАЧНОСТЬ (если P неоднозначен, то неоднозначны и ...):
    (A1) ГОМОМОРФНЫЙ ПРООБРАЗ по ПЕРЕМЕННЫМ — каждая переменная нового образца
         переходит в слово над переменными P, ПУСТОЕ ДОПУСКАЕТСЯ;
    (A2) ГОМОМОРФНЫЙ ОБРАЗ по БУКВАМ — каждая буква P переходит в слово над
         буквами, морфизм может быть НЕинъективным (напр. B->A).
    Примеры:  неоднозначен xAyByx  =>  неоднозначен xAzyByzzx  (z->eps);
              неоднозначен xAyByx  =>  неоднозначен xAyAyx     (B->A).

  Обе стороны можно композировать (образ/прообраз по переменным + по буквам).

Соглашения проекта (как в ambiguity_heuristic.py):
  * переменные   — строчные буквы a..z (их подставляют словами над алфавитом);
  * буквы/константы — заглавные A..Z (алфавит).

КОРРЕКТНОСТЬ — без ложных меток.
  * Однозначность доказывается СТРУКТУРНО (см. determinacy_closure / код
    Сардинаса–Паттерсона) и каждый вывод проверяется тем, что морфизм реально
    переводит лемму в целевой образец.
  * Неоднозначность доказывается ПОДЪЁМОМ конкретного свидетеля (sigma, tau)
    леммы через морфизм и ПРОВЕРКОЙ подстановкой, что образы цели совпали, а
    подстановки различны.
  Поэтому образец НЕ МОЖЕТ получить обе метки одновременно (это означало бы
    однозначный образец с парой совпадающих различных подстановок).
"""

import argparse
import csv
import os

import ambiguity_heuristic as ah


# ===========================================================================
# базовые операции
# ===========================================================================
def variables(pattern):
    return set(c for c in pattern if c.islower())


def letters(pattern):
    return set(c for c in pattern if c.isupper())


def substitute(pattern, assign):
    return ah.substitute(pattern, assign)


def apply_var_morphism(pattern, phi):
    """phi: переменная -> слово над переменными; буквы остаются собой."""
    return "".join(phi[c] if c.islower() else c for c in pattern)


def apply_letter_morphism(pattern, psi):
    """psi: буква -> слово над буквами; переменные остаются собой."""
    return "".join(psi[c] if c.isupper() else c for c in pattern)


def split_by_letters(s):
    """Разбить на чередование (var-блок, буква, var-блок, буква, ..., var-блок)."""
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


# ===========================================================================
# ЧАСТЬ 1.  ОДНОЗНАЧНОСТЬ (P однозначен  =>  Q однозначен)
# ===========================================================================
def var_image_match(P, Q):
    """phi (перем.P -> НЕПУСТОЕ слово над перем.) с phi(P)=Q, или None."""
    assign = {}

    def bt(i, j):
        if i == len(P):
            return j == len(Q)
        ch = P[i]
        if ch.isupper():
            return j < len(Q) and Q[j] == ch and bt(i + 1, j + 1)
        if ch in assign:
            b = assign[ch]
            return Q[j:j + len(b)] == b and bt(i + 1, j + len(b))
        for L in range(1, len(Q) - j + 1):
            block = Q[j:j + L]
            if block[-1].isupper():
                break
            assign[ch] = block
            if bt(i + 1, j + L):
                return True
            del assign[ch]
        return False

    return dict(assign) if bt(0, 0) else None


def determinacy_closure(phi, Qvars):
    """Выводимо ли из блочных равенств равенство на КАЖДОЙ переменной Q.

    Блок (значение phi(v)) с ровно одной ещё-неопределённой переменной вынуждает
    равенство значений sigma/tau на ней (сокращение в свободной полугруппе).
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


def letter_preimage_match(P, Q):
    """psi (буквы Q -> НЕПУСТОЕ слово над буквами P) с psi(Q)=P, или None."""
    assign = {}

    def bt(i, j):
        if i == len(Q):
            return j == len(P)
        ch = Q[i]
        if ch.islower():
            return j < len(P) and P[j] == ch and bt(i + 1, j + 1)
        if ch in assign:
            b = assign[ch]
            return P[j:j + len(b)] == b and bt(i + 1, j + len(b))
        for L in range(1, len(P) - j + 1):
            block = P[j:j + L]
            if block[-1].islower():
                break
            assign[ch] = block
            if bt(i + 1, j + L):
                return True
            del assign[ch]
        return False

    return dict(assign) if bt(0, 0) else None


def is_code(words):
    """Инъективен ли морфизм с такими образами (Сардинас–Паттерсон)."""
    C = set(w for w in words if w)
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
        if C & S:
            return False
        seen.add(frozenset(S))
        S = succ(S)
    return True


def is_injective_letter_morphism(psi):
    vals = list(psi.values())
    if len(set(vals)) != len(vals):
        return False
    return is_code(vals)


def verify_unamb(P, Q, phi=None, psi=None):
    """Проверить, что (phi/psi) переводит лемму P в образец Q (композиция)."""
    R = apply_var_morphism(P, phi) if phi else P
    if psi:
        return apply_letter_morphism(Q, psi) == R
    return Q == R


def variables_ok(P, Q):
    return [c for c in P if c.isupper()] == [c for c in Q if c.isupper()]


def enumerate_var_images(P, Q):
    """Промежуточный R = phi(P): переменные от Q, буквы от P."""
    pseg = split_by_letters(P)
    qseg = split_by_letters(Q)
    if len(pseg) != len(qseg):
        return
    out = [pseg[k] if k % 2 == 1 else qseg[k] for k in range(len(pseg))]
    yield "".join(out)


def derive_unamb(P, Q):
    """Вывести ОДНОЗНАЧНОСТЬ Q из однозначной леммы P. Свидетель или None."""
    if Q == P:
        return {"strategy": "тривиально", "phi": None, "psi": None}

    if variables_ok(P, Q):
        phi = var_image_match(P, Q)
        if phi is not None and determinacy_closure(phi, variables(Q)):
            if verify_unamb(P, Q, phi=phi):
                return {"strategy": "образ-перем", "phi": phi, "psi": None}

    psi = letter_preimage_match(P, Q)
    if psi is not None and is_injective_letter_morphism(psi):
        if verify_unamb(P, Q, psi=psi):
            return {"strategy": "прообраз-букв", "phi": None, "psi": psi}

    for R in enumerate_var_images(P, Q):
        phi = var_image_match(P, R)
        if phi is None or not determinacy_closure(phi, variables(R)):
            continue
        psi = letter_preimage_match(R, Q)
        if psi is not None and is_injective_letter_morphism(psi):
            if verify_unamb(P, Q, phi=phi, psi=psi):
                return {"strategy": "композиция", "phi": phi, "psi": psi,
                        "intermediate": R}
    return None


# ===========================================================================
# ЧАСТЬ 2.  НЕОДНОЗНАЧНОСТЬ (P неоднозначен  =>  Q неоднозначен)
# ===========================================================================
def lemma_witness(P, binary_maxlen=4):
    """(sigma, tau) — свидетель неоднозначности P из эвристики, или None.

    Бинарный перебор ограничен binary_maxlen (защита от взрыва по памяти).
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
    if sigma == tau or substitute(P, sigma) != substitute(P, tau):
        return None
    return sigma, tau


def parse_witness(cell):
    """'sigma={x=A, y=AA} | tau={x=AA, y=A}' -> (sigma, tau); 'eps' = пусто."""
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


def var_preimage_match(Q, P):
    """phi (перем.Q -> слово над перем.P, ПУСТОЕ можно) с phi(Q)=P, или None."""
    assign = {}

    def bt(i, j):
        if i == len(Q):
            return j == len(P)
        ch = Q[i]
        if ch.isupper():
            return j < len(P) and P[j] == ch and bt(i + 1, j + 1)
        if ch in assign:
            b = assign[ch]
            return P[j:j + len(b)] == b and bt(i + 1, j + len(b))
        for L in range(0, len(P) - j + 1):
            block = P[j:j + L]
            if L > 0 and block[-1].isupper():
                break
            assign[ch] = block
            if bt(i + 1, j + L):
                return True
            del assign[ch]
        return False

    return dict(assign) if bt(0, 0) else None


def lift_var_preimage(sigma, phi):
    return {q: "".join(sigma.get(v, "") for v in word) for q, word in phi.items()}


def letter_image_match(P, Q):
    """g (буквы P -> НЕПУСТОЕ слово над буквами) с g(P)=Q, НЕинъект. ок, или None."""
    assign = {}

    def bt(i, j):
        if i == len(P):
            return j == len(Q)
        ch = P[i]
        if ch.islower():
            return j < len(Q) and Q[j] == ch and bt(i + 1, j + 1)
        if ch in assign:
            b = assign[ch]
            return Q[j:j + len(b)] == b and bt(i + 1, j + len(b))
        for L in range(1, len(Q) - j + 1):
            block = Q[j:j + L]
            if block[-1].islower():
                break
            assign[ch] = block
            if bt(i + 1, j + L):
                return True
            del assign[ch]
        return False

    return dict(assign) if bt(0, 0) else None


def lift_letter_image(sigma, g):
    return {v: "".join(g.get(c, c) for c in word) for v, word in sigma.items()}


def valid_witness(Q, sigma, tau):
    return sigma != tau and substitute(Q, sigma) == substitute(Q, tau)


def enumerate_letter_images(P, Q):
    """Промежуточный R = g(P): переменные от P, буквы от Q."""
    pseg = split_by_letters(P)
    qseg = split_by_letters(Q)
    if len(pseg) != len(qseg):
        return
    out = [pseg[k] if k % 2 == 0 else qseg[k] for k in range(len(pseg))]
    yield "".join(out)


def derive_amb(P, Q, witP):
    """Вывести НЕОДНОЗНАЧНОСТЬ Q из неоднозначной леммы P (свидетель witP)."""
    sigma, tau = witP
    if Q == P:
        return {"strategy": "тривиально", "phi": None, "g": None,
                "sigma": sigma, "tau": tau}

    if [c for c in Q if c.isupper()] == [c for c in P if c.isupper()]:
        phi = var_preimage_match(Q, P)
        if phi is not None:
            s2, t2 = lift_var_preimage(sigma, phi), lift_var_preimage(tau, phi)
            if valid_witness(Q, s2, t2):
                return {"strategy": "прообраз-перем", "phi": phi, "g": None,
                        "sigma": s2, "tau": t2}

    if [c for c in P if c.islower()] == [c for c in Q if c.islower()]:
        g = letter_image_match(P, Q)
        if g is not None:
            s2, t2 = lift_letter_image(sigma, g), lift_letter_image(tau, g)
            if valid_witness(Q, s2, t2):
                return {"strategy": "образ-букв", "phi": None, "g": g,
                        "sigma": s2, "tau": t2}

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


# ===========================================================================
# единая классификация
# ===========================================================================
def classify(Q, unamb_lemmas, amb_lemmas):
    """Попытаться вывести вердикт для Q. Возвращает dict с полями результата.

    verdict: ОДНОЗНАЧЕН / НЕОДНОЗНАЧЕН / не выведено / КОНФЛИКТ(!).
    """
    # неоднозначность
    amb_P = amb_w = None
    for P, witP in amb_lemmas:
        w = derive_amb(P, Q, witP)
        if w is not None:
            amb_P, amb_w = P, w
            break
    # однозначность
    un_P = un_w = None
    for P in unamb_lemmas:
        w = derive_unamb(P, Q)
        if w is not None:
            un_P, un_w = P, w
            break

    if amb_w is not None and un_w is not None:
        verdict = "КОНФЛИКТ(!)"        # не должно случаться — сигнал об ошибке
    elif amb_w is not None:
        verdict = "НЕОДНОЗНАЧЕН"
    elif un_w is not None:
        verdict = "ОДНОЗНАЧЕН"
    else:
        verdict = "не выведено"

    return {
        "pattern": Q,
        "verdict": verdict,
        "amb_lemma": amb_P or "",
        "amb_strategy": amb_w["strategy"] if amb_w else "",
        "amb_phi": fmt_morphism(amb_w.get("phi")) if amb_w else "",
        "amb_g": fmt_morphism(amb_w.get("g")) if amb_w else "",
        "amb_sigma": fmt_assign(amb_w["sigma"]) if amb_w else "",
        "amb_tau": fmt_assign(amb_w["tau"]) if amb_w else "",
        "unamb_lemma": un_P or "",
        "unamb_strategy": un_w["strategy"] if un_w else "",
        "unamb_phi": fmt_morphism(un_w.get("phi")) if un_w else "",
        "unamb_psi": fmt_morphism(un_w.get("psi")) if un_w else "",
    }


# ===========================================================================
# форматирование
# ===========================================================================
def fmt_morphism(m):
    if not m:
        return ""
    return "{" + ", ".join("%s->%s" % (k, (v or "eps"))
                           for k, v in sorted(m.items())) + "}"


def fmt_assign(assign):
    return "{" + ", ".join("%s=%s" % (k, (v or "eps"))
                           for k, v in sorted(assign.items())) + "}"


# ===========================================================================
# ввод/вывод корпусов
# ===========================================================================
def read_unambiguous_lemmas(*paths):
    """ОДНОЗНАЧНЫЕ образцы из CSV (нужна колонка verdict со словом ОДНОЗНАЧЕН)."""
    seen, out = set(), []
    for path in paths:
        if not path or not os.path.exists(path):
            continue
        with open(path, newline="", encoding="utf-8") as f:
            r = csv.DictReader(f)
            if not r.fieldnames or "verdict" not in r.fieldnames:
                continue
            for row in r:
                pat = (row.get("pattern") or "").strip()
                verdict = (row.get("verdict") or "").strip()
                # ОДНОЗНАЧЕН — подстрока в НЕОДНОЗНАЧЕН, поэтому строгое сравнение
                if pat and verdict == "ОДНОЗНАЧЕН" and pat not in seen:
                    seen.add(pat)
                    out.append(pat)
    return out


def read_ambiguous_lemmas(*paths):
    """НЕОДНОЗНАЧНЫЕ образцы со свидетелем (готовый из CSV или из эвристики)."""
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
                if has_verdict and "НЕОДНОЗНАЧЕН" not in (row.get("verdict") or ""):
                    continue
                wit = None
                if has_witness:
                    parsed = parse_witness(row.get("witness") or "")
                    if parsed is not None:
                        wit = _checked(pat, *parsed)
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


# ===========================================================================
# самопроверка (примеры обеих сторон из постановки)
# ===========================================================================
def selftest():
    print("=== САМОПРОВЕРКА ===")
    ok = True

    # --- однозначность ---
    cases_u = [
        ("xAyxBy", "xyAyxyBy", "образ-перем"),
        ("xAyxBy", "xAyxxByx", None),
        ("xAyxBy", "xCyxDy", "прообраз-букв"),
    ]
    for P, Q, strat in cases_u:
        w = derive_unamb(P, Q)
        st = w is not None and (strat is None or w["strategy"] == strat)
        ok &= st
        print("[%s] ОДНОЗН  %s => %s : %s"
              % ("OK" if st else "FAIL", P, Q, w["strategy"] if w else "нет"))

    # не должно выводиться как однозначное (xAxBy неоднозначен)
    w = derive_unamb("xAyxBy", "xAxBy")
    st = w is None
    ok &= st
    print("[%s] ОДНОЗН  (нет вывода) xAyxBy => xAxBy" % ("OK" if st else "FAIL"))

    # --- неоднозначность ---
    base = "xAyByx"
    witP = lemma_witness(base)
    ok &= witP is not None
    cases_a = [
        ("xAzyByzzx", "прообраз-перем"),
        ("xAyAyx", "образ-букв"),
        ("xCyDyx", None),
        ("xAzyAyzx", "композиция"),
    ]
    for Q, strat in cases_a:
        w = derive_amb(base, Q, witP)
        st = w is not None and (strat is None or w["strategy"] == strat)
        ok &= st
        print("[%s] НЕОДН   %s => %s : %s"
              % ("OK" if st else "FAIL", base, Q, w["strategy"] if w else "нет"))

    # не должно выводиться как неоднозначное (xAyxBy однозначен)
    w = derive_amb(base, "xAyxBy", witP)
    st = w is None
    ok &= st
    print("[%s] НЕОДН   (нет вывода) xAyByx => xAyxBy" % ("OK" if st else "FAIL"))

    print("=== ИТОГ:", "ВСЕ ТЕСТЫ ПРОЙДЕНЫ" if ok else "ЕСТЬ ОШИБКИ", "===")
    return 0 if ok else 1


# ===========================================================================
# main
# ===========================================================================
def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(
        description="Классификация образцов (одно/неоднозначность) по гомоморфизмам")
    ap.add_argument("--unamb-lemmas", nargs="*",
                    default=[os.path.join(here, "ambiguity_lemmas.csv")],
                    help="CSV с известными ОДНОЗНАЧНЫМИ образцами (нужна колонка verdict)")
    ap.add_argument("--amb-lemmas", nargs="*",
                    default=[os.path.join(here, "ambiguity_lemmas.csv"),
                             os.path.join(here, "ambiguity_proven.csv")],
                    help="CSV с известными НЕОДНОЗНАЧНЫМИ образцами")
    ap.add_argument("-i", "--input", default=None,
                    help="CSV с целевыми образцами (первый столбец — pattern)")
    ap.add_argument("-o", "--output",
                    default=os.path.join(here, "homomorphism_classified.csv"))
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("targets", nargs="*", help="целевые образцы напрямую")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    unamb = read_unambiguous_lemmas(*args.unamb_lemmas)
    amb = read_ambiguous_lemmas(*args.amb_lemmas)
    print("Однозначных лемм: %d ;  неоднозначных лемм со свидетелем: %d"
          % (len(unamb), len(amb)))

    targets = args.targets or (read_patterns(args.input) if args.input else [])
    if not targets:
        print("Нет целевых образцов. Укажите их аргументами или через -i FILE.")
        print("Подсказка: --selftest для демонстрации.")
        return 0

    fields = ["pattern", "verdict",
              "amb_lemma", "amb_strategy", "amb_phi", "amb_g", "amb_sigma", "amb_tau",
              "unamb_lemma", "unamb_strategy", "unamb_phi", "unamb_psi"]
    n_amb = n_un = n_none = n_conf = 0
    with open(args.output, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for Q in targets:
            row = classify(Q, unamb, amb)
            w.writerow(row)
            f.flush()
            v = row["verdict"]
            if v == "НЕОДНОЗНАЧЕН":
                n_amb += 1
            elif v == "ОДНОЗНАЧЕН":
                n_un += 1
            elif v == "КОНФЛИКТ(!)":
                n_conf += 1
            else:
                n_none += 1
            mark = {"НЕОДНОЗНАЧЕН": "A", "ОДНОЗНАЧЕН": "U",
                    "КОНФЛИКТ(!)": "!", "не выведено": "-"}.get(v, "?")
            base = row["amb_lemma"] or row["unamb_lemma"]
            print("[%s] %-12s %-13s %s" % (mark, Q, v, ("<= " + base) if base else ""))

    print("\n===== ИТОГ =====")
    print("  всего образцов:        %d" % len(targets))
    print("  НЕОДНОЗНАЧЕН (выведено):%d" % n_amb)
    print("  ОДНОЗНАЧЕН  (выведено): %d" % n_un)
    print("  не выведено:           %d" % n_none)
    if n_conf:
        print("  КОНФЛИКТЫ (ОШИБКА!):   %d" % n_conf)
    print("\nЗаписано -> %s" % args.output)
    return 1 if n_conf else 0


if __name__ == "__main__":
    raise SystemExit(main())
