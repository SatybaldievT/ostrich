#!/usr/bin/env python3
"""
Генератор SMT-LIB задач из паттерна слова.

Из паттерна вида:
    x x x A y x B y x
строит SMT-LIB файл с двумя копиями уравнения (переменные с суффиксами 1 и 2):

    (= (str.++ x1 x1 x1 "A" y1 x1 "B" y1 x1)
       (str.++ x2 x2 x2 "A" y2 x2 "B" y2 x2))

Правило разбора токенов паттерна:
  * токен из строчных букв/цифр ([a-z][a-z0-9_]*)  -> переменная;
  * всё остальное (заглавные буквы, символы, уже закавыченное) -> строковый литерал.

Использование:
    python gen_smt.py "x x x A y x B y x"
    python gen_smt.py "x x x A y x B y x" -o task.smt2
    echo "x x x A y x B y x" | python gen_smt.py
"""

import argparse
import re
import sys

VAR_RE = re.compile(r"^[a-z][a-z0-9_]*$")


def is_variable(token: str) -> bool:
    """Строчный идентификатор -> переменная, иначе -> литерал."""
    return bool(VAR_RE.match(token))


def as_literal(token: str) -> str:
    """Обернуть токен в кавычки, если он ещё не закавычен."""
    if token.startswith('"') and token.endswith('"'):
        return token
    return f'"{token}"'


def tokenize(pattern: str):
    """
    Разбить паттерн на токены.

    Поддерживаются два формата:
      * посимвольный, без пробелов:  "xAyyByx" -> x A y y B y x
      * через пробел:                "x x A y x" -> x x A y x
    Если в паттерне есть кавычки (многосимвольные литералы) — делим по пробелам,
    иначе каждый непробельный символ считается отдельным токеном.
    """
    if '"' in pattern:
        return pattern.split()
    return [c for c in pattern if not c.isspace()]


def build_side(tokens, suffix: str):
    """Собрать одну сторону уравнения для данного суффикса (1 или 2)."""
    parts = []
    for tok in tokens:
        if is_variable(tok):
            parts.append(f"{tok}{suffix}")
        else:
            parts.append(as_literal(tok))
    return parts


def canonical_var_map(tokens):
    """Переменная -> индекс 1..n в порядке первого вхождения."""
    vmap = {}
    for tok in tokens:
        if is_variable(tok) and tok not in vmap:
            vmap[tok] = len(vmap) + 1
    return vmap


def canonical_literal_map(tokens):
    """Литерал -> канон. буква A,B,C,... в порядке первого вхождения."""
    cmap = {}
    for tok in tokens:
        if not is_variable(tok):
            lv = literal_value(tok)
            if lv not in cmap:
                cmap[lv] = chr(ord("A") + len(cmap))
    return cmap


def build_side_canonical(tokens, prefix: str, vmap, cmap):
    """Сторона уравнения с КАНОНИЧЕСКИМИ именами: переменные prefix+индекс,
    литералы — канонические буквы. prefix='x' (копия 1) или 'y' (копия 2)."""
    parts = []
    for tok in tokens:
        if is_variable(tok):
            parts.append(f"{prefix}{vmap[tok]}")
        else:
            parts.append(as_literal(cmap[literal_value(tok)]))
    return parts


def literal_value(token: str) -> str:
    """Содержимое литерала без обрамляющих кавычек (для regex-ограничений)."""
    if len(token) >= 2 and token.startswith('"') and token.endswith('"'):
        return token[1:-1]
    return token


def alphabet_regex(literals) -> str:
    """Регулярное выражение (re.* (re.union ...)) по алфавиту литералов паттерна."""
    res = [f'(str.to_re "{lv}")' for lv in literals]
    if len(res) == 1:
        return f"(re.* {res[0]})"
    return f"(re.* (re.union {' '.join(res)}))"


def generate(pattern: str, distinct_var=None, mode: str = "suffix-regex",
             canonical: bool = False) -> str:
    tokens = tokenize(pattern)
    if not tokens:
        raise ValueError("Пустой паттерн")

    # Уникальные переменные в порядке появления
    variables = []
    for tok in tokens:
        if is_variable(tok) and tok not in variables:
            variables.append(tok)

    if not variables:
        raise ValueError("В паттерне нет переменных (строчных идентификаторов)")

    # Литералы (алфавит) в порядке появления — для regex-ограничений
    literals = []
    for tok in tokens:
        if not is_variable(tok):
            lv = literal_value(tok)
            if lv not in literals:
                literals.append(lv)

    # --- КАНОНИЧЕСКИЙ режим: переименования дают ОДИНАКОВЫЙ smt2 ---
    # переменные -> x1..xn (копия 1) / y1..yn (копия 2); литералы -> A,B,C,...
    if canonical:
        vmap = canonical_var_map(tokens)
        cmap = canonical_literal_map(tokens)
        # имена копий: x{i} и y{i}; различающая переменная -> её канон. имена
        if distinct_var is None:
            distinct_idx = vmap[variables[0]]
        elif distinct_var not in variables:
            raise ValueError(f"Переменная '{distinct_var}' отсутствует в паттерне")
        else:
            distinct_idx = vmap[distinct_var]
        d1, d2 = f"x{distinct_idx}", f"y{distinct_idx}"
        n = len(vmap)

        lines = ["(set-logic QF_SLIA)", ""]
        for v in range(1, n + 1):
            lines.append(f"(declare-fun x{v} () String)")
        for v in range(1, n + 1):
            lines.append(f"(declare-fun y{v} () String)")
        lines.append("")

        if mode == "neq":
            lines.append(f"(assert (not (= {d1} {d2})))")
        else:
            lines.append(f"(assert (str.suffixof {d1} {d2}))")
            lines.append(f"(assert (< (str.len {d1}) (str.len {d2})))")
            if cmap:
                re = alphabet_regex([cmap[lv] for lv in literals])
                for v in range(1, n + 1):
                    lines.append(f"(assert (str.in_re x{v} {re}))")
                for v in range(1, n + 1):
                    lines.append(f"(assert (str.in_re y{v} {re}))")

        left = " ".join(build_side_canonical(tokens, "x", vmap, cmap))
        right = " ".join(build_side_canonical(tokens, "y", vmap, cmap))
        lines.append(f"(assert (= (str.++ {left}) (str.++ {right})))")
        lines += ["", "(check-sat)", "(get-model)", ""]
        return "\n".join(lines)

    # Переменная, по которой требуем различие двух копий (по умолчанию первая)
    if distinct_var is None:
        distinct_var = variables[0]
    elif distinct_var not in variables:
        raise ValueError(f"Переменная '{distinct_var}' отсутствует в паттерне")

    lines = ["(set-logic QF_SLIA)", ""]

    # Объявления: сперва все копии 1, затем все копии 2
    for suffix in ("1", "2"):
        for v in variables:
            lines.append(f"(declare-fun {v}{suffix} () String)")
    lines.append("")

    if mode == "neq":
        # Прежняя форма: копии различаются через неравенство
        lines.append(f"(assert (not (= {distinct_var}1 {distinct_var}2)))")
    else:
        # Новая форма (как testOst3_propsuffix): различие выражаем через
        #   * собственный суффикс: distinct1 — суффикс distinct2 и строго короче;
        #   * regex-ограничения на алфавит для всех переменных.
        lines.append(f"(assert (str.suffixof {distinct_var}1 {distinct_var}2))")
        lines.append(
            f"(assert (< (str.len {distinct_var}1) (str.len {distinct_var}2)))")
        if literals:
            re = alphabet_regex(literals)
            for suffix in ("1", "2"):
                for v in variables:
                    lines.append(f"(assert (str.in_re {v}{suffix} {re}))")

    left = " ".join(build_side(tokens, "1"))
    right = " ".join(build_side(tokens, "2"))
    lines.append(f"(assert (= (str.++ {left}) (str.++ {right})))")
    lines.append("")

    lines.append("(check-sat)")
    lines.append("(get-model)")
    lines.append("")

    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description="Генератор SMT-LIB из паттерна слова")
    ap.add_argument("pattern", nargs="?", help='паттерн, напр. "x x x A y x B y x"')
    ap.add_argument("-o", "--output", help="файл для записи (по умолчанию stdout)")
    ap.add_argument("-d", "--distinct",
                    help="переменная, чьи копии должны различаться (по умолчанию первая)")
    ap.add_argument("-m", "--mode", choices=["suffix-regex", "neq"],
                    default="suffix-regex",
                    help="форма различия копий: suffix-regex (str.suffixof + "
                         "< len + regex, по умолчанию) или neq (неравенство)")
    ap.add_argument("-c", "--canonical", action="store_true",
                    help="канонические имена: переменные x1..xn/y1..yn, буквы "
                         "A,B,C,... (переименования дают идентичный smt2)")
    args = ap.parse_args()

    pattern = args.pattern if args.pattern is not None else sys.stdin.read().strip()
    smt = generate(pattern, args.distinct, args.mode, canonical=args.canonical)

    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(smt)
        print(f"Записано в {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(smt)


if __name__ == "__main__":
    main()
