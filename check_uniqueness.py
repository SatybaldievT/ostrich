#!/usr/bin/env python3
"""
Проверка однозначности паттернов по результатам прогона решателя.

Однозначность (в постановке поиска коллизий слов):
  * sat      -> найдена НЕТРИВИАЛЬНАЯ коллизия: два разных набора значений
               переменных дают одно и то же слово  ==>  паттерн НЕОДНОЗНАЧНЫЙ;
  * unsat    -> коллизии нет                        ==>  паттерн ОДНОЗНАЧНЫЙ;
  * unknown/timeout -> не определено.

Для sat-строк дополнительно ВЕРИФИЦИРУЕМ свидетеля из counter_example:
подставляем оба присваивания в паттерн (строчные -> значение переменной,
заглавные -> сам символ-константа), и проверяем, что
  word1 == word2   (слова реально совпадают)  И
  assign1 != assign2 (присваивания реально различаются).
Если хоть одно не выполнено -> witness_valid=False (повод разобраться:
ошибка разбора модели/решателя), иначе True.

Вход : CSV с колонками pattern,mode,status,time,counter_example
Выход: тот же набор строк + колонки
       unambiguous (yes/no/unknown), witness_valid, word1, word2, note

Запуск:
    python check_uniqueness.py
    python check_uniqueness.py -i ostrich_session_results.csv -o uniqueness.csv
"""

import argparse
import csv
import re

# "[x=AAAA, y=A] != [x=AAA, y=AA]"
SIDE_RE = re.compile(r"\[(.*?)\]\s*!=\s*\[(.*?)\]", re.DOTALL)
ASSIGN_RE = re.compile(r"\s*([A-Za-z]\w*)\s*=\s*(\S*)\s*")


def parse_counter_example(text):
    """Вернуть (assign1, assign2) как словари {переменная: значение} или (None,None)."""
    if not text:
        return None, None
    m = SIDE_RE.search(text)
    if not m:
        return None, None

    def parse_side(s):
        out = {}
        for part in s.split(","):
            part = part.strip()
            if not part:
                continue
            am = ASSIGN_RE.fullmatch(part)
            if am:
                out[am.group(1)] = am.group(2)
        return out

    return parse_side(m.group(1)), parse_side(m.group(2))


def substitute(pattern, assign):
    """Слово, получаемое подстановкой присваивания: lower->значение, прочее->символ."""
    out = []
    for ch in pattern:
        if ch.isspace():
            continue
        if ch.islower():
            out.append(assign.get(ch, ""))
        else:
            out.append(ch)        # константа — сам символ
    return "".join(out)


def classify(row):
    """Дополнить строку полями однозначности и верификации свидетеля."""
    status = (row.get("status") or "").strip().lower()
    pattern = (row.get("pattern") or "").strip()
    ce = row.get("counter_example") or ""

    res = dict(row)
    res["word1"] = ""
    res["word2"] = ""
    res["witness_valid"] = ""
    res["note"] = ""

    if status == "sat":
        res["unambiguous"] = "no"      # есть коллизия -> неоднозначный
        a1, a2 = parse_counter_example(ce)
        if a1 is None or a2 is None or not a1 or not a2:
            res["witness_valid"] = "False"
            res["note"] = "не разобрался counter_example"
            return res
        w1 = substitute(pattern, a1)
        w2 = substitute(pattern, a2)
        res["word1"], res["word2"] = w1, w2
        words_eq = (w1 == w2)
        assigns_diff = (a1 != a2)
        res["witness_valid"] = str(words_eq and assigns_diff)
        notes = []
        if not words_eq:
            notes.append("слова НЕ совпадают")
        if not assigns_diff:
            notes.append("присваивания совпадают (тривиально)")
        res["note"] = "; ".join(notes)
    elif status == "unsat":
        res["unambiguous"] = "yes"     # коллизии нет -> однозначный
    else:
        res["unambiguous"] = "unknown"
        res["note"] = "статус %s — не определено" % (status or "?")
    return res


def main():
    ap = argparse.ArgumentParser(
        description="Проверка однозначности паттернов по результатам решателя")
    ap.add_argument("-i", "--input", default="ostrich_session_results.csv")
    ap.add_argument("-o", "--output", default="uniqueness.csv")
    args = ap.parse_args()

    with open(args.input, newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))

    out_rows = [classify(r) for r in rows]

    base = ["pattern", "mode", "status", "time", "counter_example"]
    extra = ["unambiguous", "witness_valid", "word1", "word2", "note"]
    fieldnames = base + extra
    with open(args.output, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
        w.writeheader()
        w.writerows(out_rows)

    # --- сводка ---
    n = len(out_rows)
    amb = [r for r in out_rows if r["unambiguous"] == "no"]
    uniq = [r for r in out_rows if r["unambiguous"] == "yes"]
    unk = [r for r in out_rows if r["unambiguous"] == "unknown"]
    bad = [r for r in amb if r["witness_valid"] != "True"]

    # дубликаты паттернов в файле
    seen, dups = set(), []
    for r in out_rows:
        key = (r["pattern"], r["mode"])
        if key in seen:
            dups.append(key)
        seen.add(key)

    print("Всего строк: %d" % n)
    print("  НЕОДНОЗНАЧНЫЕ (sat, есть коллизия): %d" % len(amb))
    print("    из них свидетель проверен и верен: %d" %
          sum(1 for r in amb if r["witness_valid"] == "True"))
    print("    свидетель НЕ прошёл проверку:      %d" % len(bad))
    print("  ОДНОЗНАЧНЫЕ (unsat):                 %d" % len(uniq))
    print("  НЕ ОПРЕДЕЛЕНО (unknown/timeout):     %d" % len(unk))
    print("  дубликаты (pattern,mode):            %d" % len(dups))
    if bad:
        print("\n  Строки с непрошедшим свидетелем:")
        for r in bad:
            print("    %-12s %-6s %s" % (r["pattern"], r["mode"], r["note"]))
    print("\nЗаписано -> %s" % args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
