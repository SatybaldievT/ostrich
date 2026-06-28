#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Каноническая форма образца — инвариант относительно ПЕРЕИМЕНОВАНИЙ.

Правила канонизации:
  1) переменные (строчные буквы) -> цифры 1..n в порядке ПЕРВОГО вхождения;
  2) буквы-константы (заглавные)  -> A,B,C,...,Z в порядке ПЕРВОГО вхождения.

Пример:
    yxBxxAy  ->  канон '12A22B1'
             ->  smt2 (левая копия)  x1 x2 A x2 x2 B x1
             ->  smt2 (правая копия) y1 y2 A y2 y2 B y1

Зачем: два образца — переименования друг друга  <=>  у них РАВНЫ канонические
формы. Значит, образец, который является переименованием уже проанализированного,
находится в базе мгновенно (точным сравнением ключа), без перебора морфизмов.
canonical() — ПОЛНЫЙ инвариант: равенство канонов равносильно существованию
биекции переменных и биекции букв, переводящей один образец в другой.

Соглашения проекта (как в ambiguity_heuristic.py):
  * переменные      — строчные буквы a..z;
  * буквы/константы — заглавные A..Z.
"""


def canonical(pattern):
    """Каноническая строка образца ('12A22B1'). Пробелы игнорируются."""
    vmap, cmap, out = {}, {}, []
    for ch in pattern:
        if ch.islower():
            if ch not in vmap:
                vmap[ch] = str(len(vmap) + 1)
            out.append(vmap[ch])
        elif ch.isupper():
            if ch not in cmap:
                cmap[ch] = chr(ord("A") + len(cmap))
            out.append(cmap[ch])
        # прочее (пробелы и т.п.) — пропускаем
    return "".join(out)


def canonical_maps(pattern):
    """Вернуть (vmap, cmap): переменная->индекс(int), буква->канон.буква."""
    vmap, cmap = {}, {}
    for ch in pattern:
        if ch.islower() and ch not in vmap:
            vmap[ch] = len(vmap) + 1
        elif ch.isupper() and ch not in cmap:
            cmap[ch] = chr(ord("A") + len(cmap))
    return vmap, cmap


def smt_tokens(pattern, side="left"):
    """Список токенов одной копии уравнения с КАНОНИЧЕСКИМИ именами.

    side='left'  -> переменные x1..xn;  side='right' -> y1..yn.
    Буквы заменяются на канонические литералы A,B,C,...
    """
    prefix = "x" if side == "left" else "y"
    vmap, cmap = canonical_maps(pattern)
    toks = []
    for ch in pattern:
        if ch.islower():
            toks.append("%s%d" % (prefix, vmap[ch]))
        elif ch.isupper():
            toks.append(cmap[ch])
    return toks


def canonical_renaming(P, Q):
    """Биекции (vmap, cmap) переменных и букв, переводящие P в Q, или None.

    Существуют тогда и только тогда, когда canonical(P) == canonical(Q).
    vmap: переменная P -> переменная Q;  cmap: буква P -> буква Q.
    """
    if canonical(P) != canonical(Q):
        return None
    vmap, cmap = {}, {}
    for a, b in zip(P, Q):
        if a.islower():
            vmap[a] = b
        elif a.isupper():
            cmap[a] = b
    return vmap, cmap


if __name__ == "__main__":
    # быстрая проверка примера из постановки
    p = "yxBxxAy"
    assert canonical(p) == "12A22B1", canonical(p)
    assert smt_tokens(p, "left") == ["x1", "x2", "A", "x2", "x2", "B", "x1"]
    assert smt_tokens(p, "right") == ["y1", "y2", "A", "y2", "y2", "B", "y1"]
    # переименования совпадают по канону
    assert canonical("yxBxxAy") == canonical("abCbbDa")
    assert canonical("xAyxBy") != canonical("xAxBy")
    print("canonical: OK  (%s -> %s)" % (p, canonical(p)))
    print("  left :", " ".join(smt_tokens(p, "left")))
    print("  right:", " ".join(smt_tokens(p, "right")))
