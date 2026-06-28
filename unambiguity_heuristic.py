#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Эвристика ОДНОЗНАЧНОСТИ образца на базе балансирующих разрезов.

Лемма (элементарный вариант).
  Пусть есть балансирующий разрез  w1 | w2  (векторы кратностей переменных
  обеих частей линейно зависимы и оба ненулевые) такой, что
        w1 = xi C1 w1' ,  w2 = xi C2 w2' ,   C1 != C2  (C1, C2 — константы).
  Тогда образец ОДНОЗНАЧЕН по переменной xi. Если переменных ровно две —
  образец однозначен вообще.
  Доказательство — то же, что для xAyxBy.

  Симметричное (суффиксное) условие тоже работает:
        w1 = w1' C1 xi ,  w2 = w2' C2 xi ,   C1 != C2.

Балансирующие разрезы берём из ambiguity_heuristic (общий код).
"""

import argparse
import csv
import os

from ambiguity_heuristic import variables, balancing_gaps, read_patterns


def _is_var(ch):
    return ch.islower()


def _is_const(ch):
    return ch.isupper()


def _prefix_cond(w1, w2):
    """xi C1 w1' | xi C2 w2', C1 != C2 -> (xi, C1, C2) или None."""
    if len(w1) >= 2 and len(w2) >= 2:
        if (_is_var(w1[0]) and w1[0] == w2[0]
                and _is_const(w1[1]) and _is_const(w2[1]) and w1[1] != w2[1]):
            return (w1[0], w1[1], w2[1])
    return None


def _suffix_cond(w1, w2):
    """w1' C1 xi | w2' C2 xi, C1 != C2 -> (xi, C1, C2) или None."""
    if len(w1) >= 2 and len(w2) >= 2:
        if (_is_var(w1[-1]) and w1[-1] == w2[-1]
                and _is_const(w1[-2]) and _is_const(w2[-2]) and w1[-2] != w2[-2]):
            return (w1[-1], w1[-2], w2[-2])
    return None


def unambiguity_lemma(pattern):
    """Свидетель однозначности по лемме (или None)."""
    vars_ = variables(pattern)
    for i in balancing_gaps(pattern):
        w1, w2 = pattern[:i], pattern[i:]
        for side, hit in (("prefix", _prefix_cond(w1, w2)),
                          ("suffix", _suffix_cond(w1, w2))):
            if hit:
                xi, c1, c2 = hit
                return {
                    "cut": i,
                    "side": side,
                    "var": xi,
                    "c1": c1,
                    "c2": c2,
                    "w1": w1,
                    "w2": w2,
                    "overall": len(vars_) == 2,
                }
    return None


def analyse(pattern):
    res = {
        "pattern": pattern,
        "verdict": "не доказано",
        "var": "",
        "side": "",
        "cut": "",
        "w1": "",
        "w2": "",
        "c1": "",
        "c2": "",
    }
    w = unambiguity_lemma(pattern)
    if w is None:
        return res
    res.update({
        "var": w["var"],
        "side": w["side"],
        "cut": w["cut"],
        "w1": w["w1"],
        "w2": w["w2"],
        "c1": w["c1"],
        "c2": w["c2"],
    })
    res["verdict"] = ("ОДНОЗНАЧЕН" if w["overall"]
                      else "однозначен по %s" % w["var"])
    return res


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description="Эвристика однозначности (лемма о балансирующих разрезах)")
    ap.add_argument("-i", "--input", default=os.path.join(here, "ambiguity_not_proven.csv"))
    ap.add_argument("-o", "--output", default=os.path.join(here, "unambiguity_results.csv"))
    ap.add_argument("patterns", nargs="*", help="образцы напрямую (вместо файла)")
    args = ap.parse_args()

    pats = args.patterns if args.patterns else read_patterns(args.input)

    fields = ["pattern", "verdict", "var", "side", "cut", "w1", "w2", "c1", "c2"]
    n_overall = n_pervar = n_none = 0

    with open(args.output, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        f.flush()
        for i, p in enumerate(pats, 1):
            r = analyse(p)
            w.writerow(r)
            f.flush()
            if r["verdict"] == "ОДНОЗНАЧЕН":
                n_overall += 1
            elif r["verdict"].startswith("однозначен по"):
                n_pervar += 1
            else:
                n_none += 1
            print("[%d/%d] %-12s %-16s %s" %
                  (i, len(pats), r["pattern"], r["verdict"],
                   ("%s: %s|%s (%s!=%s)" % (r["side"], r["w1"], r["w2"], r["c1"], r["c2"])
                    if r["var"] else "")), flush=True)

    print("\n===== ИТОГ =====")
    print("  всего образцов:                 %d" % len(pats))
    print("  ОДНОЗНАЧЕН (лемма, 2 перем.):   %d" % n_overall)
    print("  однозначен по переменной:       %d" % n_pervar)
    print("  лемма не сработала:             %d" % n_none)
    print("\nЗаписано -> %s" % args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
