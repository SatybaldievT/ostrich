#!/usr/bin/env python3
"""
Бенчмарк поиска нетривиальных коллизий слов — версия под решатель Ostrich.

Аналог исходного скрипта на Z3, но без ручной LIA-редукции (LeviLiaSolver):
редукцию уравнения слов (Левай/Нильсен) выполняет сам Ostrich
(ключи +backwardPropagation,+nielsenSplitter и курсовой +commutation),
поэтому здесь мы только:

  1. по паттерну строим SMT-LIB задачу с ДВУМЯ копиями уравнения
     (переменные с суффиксами 1 и 2) и требуем нетривиальное различие копий;
  2. ограничиваем алфавит переменных множеством констант паттерна;
  3. применяем инвариант режима (mode);
  4. запускаем Ostrich через ostrich_runner и разбираем модель как контрпример.

Режимы (mode) повторяют исходный скрипт:
  * base         — без дополнительных ограничений;
  * small_first  — длина первой переменной <= 10;
  * borders      — первые символы двух первых переменных совпадают;
  * periodicity  — у каждой переменной первый символ == последнему.

Использование:
    python ostrich_benchmarks.py                       # встроенный паттерн
    python ostrich_benchmarks.py --csv jbjkbres1.csv   # колонка pattern
    python ostrich_benchmarks.py --csv in.csv -o out.csv -j 4 --timeout 60
    python ostrich_benchmarks.py --baseline            # ключи без +commutation
"""

import argparse
import concurrent.futures as cf
import csv
import os
import re
import string
import sys

import ostrich_runner as runner

BASEDIR = os.path.dirname(os.path.abspath(__file__))
OUTDIR = os.path.join(BASEDIR, "ostrich_bench_out")
MODES = ["base", "small_first", "borders", "periodicity"]

# Модель Ostrich: (define-fun x1 () String "ABBA")
MODEL_RE = re.compile(r'\(define-fun\s+(\S+)\s+\(\)\s+String\s+"((?:[^"]|"")*)"\)')


def parse_model(stdout):
    """Вернуть {имя -> значение} из вывода (get-model)."""
    out = {}
    for name, val in MODEL_RE.findall(stdout):
        out[name] = val.replace('""', '"')
    return out


def quote(token):
    """SMT-литерал из константы паттерна."""
    return '"%s"' % token


def build_side(tokens, variables, suffix):
    """Собрать одну сторону уравнения: переменные получают суффикс копии."""
    parts = []
    for tok in tokens:
        if tok in variables:
            parts.append("%s%s" % (tok, suffix))
        else:
            parts.append(quote(tok))
    return " ".join(parts)


def alphabet_re(constants):
    """re-выражение «строка из символов-констант паттерна»."""
    if not constants:
        # нет констант -> любой однобуквенный алфавит (как Star(Range("A","Z")))
        return "(re.* (re.range \"A\" \"Z\"))"
    if len(constants) == 1:
        inner = '(str.to_re "%s")' % constants[0]
    else:
        inner = "(re.union %s)" % " ".join('(str.to_re "%s")' % c for c in constants)
    return "(re.* %s)" % inner


def mode_asserts(mode, variables):
    """Дополнительные ассерты инварианта режима (применяются к копии 1)."""
    if not variables or mode == "base":
        return []
    out = []
    if mode == "small_first":
        v = variables[0]
        out.append("(assert (<= (str.len %s1) 10))" % v)
    elif mode == "borders":
        if len(variables) >= 2:
            v1, v2 = variables[0], variables[1]
            out.append("(assert (= (str.substr %s1 0 1) (str.substr %s1 0 1)))"
                       % (v1, v2))
    elif mode == "periodicity":
        for v in variables:
            out.append("(assert (= (str.substr %s1 0 1) "
                       "(str.substr %s1 (- (str.len %s1) 1) 1)))" % (v, v, v))
    return out


def generate(pattern, mode="base", max_len=20):
    """
    Построить SMT-LIB задачу поиска нетривиальной коллизии для паттерна.

    Токенизация посимвольная: строчная буква/цифра -> переменная,
    заглавная (и прочее) -> константа.
    Возвращает (smt_text, variables) либо (None, []) если переменных нет.
    """
    tokens = [c for c in pattern if not c.isspace()]
    variables, constants = [], []
    for t in tokens:
        if t.islower() and t not in variables:
            variables.append(t)
        elif not t.islower() and not t.isspace() and t not in constants:
            constants.append(t)
    variables.sort()
    constants.sort()

    if not variables:
        return None, []

    alpha = alphabet_re(constants)
    lines = ["(set-logic QF_SLIA)", ""]
    for suffix in ("1", "2"):
        for v in variables:
            lines.append("(declare-fun %s%s () String)" % (v, suffix))
    lines.append("")

    # алфавит и границы длин переменных (1..max_len) для обеих копий
    for suffix in ("1", "2"):
        for v in variables:
            sv = "%s%s" % (v, suffix)
            lines.append("(assert (str.in_re %s %s))" % (sv, alpha))
            lines.append("(assert (and (>= (str.len %s) 1) (<= (str.len %s) %d)))"
                         % (sv, sv, max_len))
    lines.append("")

    # нетривиальность: хотя бы одна переменная различается в двух копиях
    diff = " ".join("(not (= %s1 %s2))" % (v, v) for v in variables)
    lines.append("(assert (or %s))" % diff if len(variables) > 1
                 else "(assert %s)" % diff)

    left = build_side(tokens, variables, "1")
    right = build_side(tokens, variables, "2")
    lines.append("(assert (= (str.++ %s) (str.++ %s)))" % (left, right))

    for a in mode_asserts(mode, variables):
        lines.append(a)
    lines.append("")

    lines.append("(check-sat)")
    lines.append("(get-model)")
    lines.append("")
    return "\n".join(lines), variables


def format_counter_example(model, variables):
    """Сформировать строку контрпримера [v=val1,...] != [v=val2,...]."""
    sol1 = ["%s=%s" % (v, model.get("%s1" % v, "?")) for v in variables]
    sol2 = ["%s=%s" % (v, model.get("%s2" % v, "?")) for v in variables]
    return "[%s] != [%s]" % (", ".join(sol1), ", ".join(sol2))


def safe_name(idx, pattern, mode):
    s = re.sub(r"[^A-Za-z0-9]", "_", pattern)[:32]
    return "bench_%03d_%s_%s" % (idx, s, mode)


def check(idx, pattern, mode, flags, timeout, max_len, keep_smt):
    """Один прогон: (pattern, mode) -> результат словарём."""
    smt, variables = generate(pattern, mode, max_len)
    if smt is None:
        return {"pattern": pattern, "mode": mode, "status": "unique",
                "time": 0.0, "counter_example": ""}

    os.makedirs(OUTDIR, exist_ok=True)
    smt_path = os.path.join(OUTDIR, safe_name(idx, pattern, mode) + ".smt2")
    with open(smt_path, "w", encoding="utf-8") as f:
        f.write("; pattern: %s   mode: %s\n%s" % (pattern, mode, smt))

    # +incremental +model — иначе Ostrich игнорирует (get-model) и модель не выводится
    res = runner.run(smt_path, flags=flags, timeout=timeout,
                     extra_args=["+incremental", "+model"])
    status = "timeout" if res["timeout"] else (res["status"] or "unknown")

    counter = ""
    if status == "sat":
        counter = format_counter_example(parse_model(res["stdout"]), variables)

    if not keep_smt:
        try:
            os.remove(smt_path)
        except OSError:
            pass

    return {"pattern": pattern, "mode": mode, "status": status,
            "time": res["time"], "counter_example": counter}


def read_patterns(args):
    """Список паттернов из CSV (колонка pattern) / CLI / встроенного набора."""
    pats = []
    for path in (args.csv or []):
        with open(path, newline="", encoding="utf-8") as f:
            for row in csv.DictReader(f):
                p = (row.get("pattern") or "").strip()
                if p:
                    pats.append(p)
    for p in (args.pattern or []):
        pats.append(p.strip())
    if not pats:
        pats = ["xxxyAyBx"]
    return pats


def main():
    ap = argparse.ArgumentParser(
        description="Бенчмарк поиска коллизий слов на решателе Ostrich")
    ap.add_argument("--csv", action="append",
                    help="CSV с колонкой pattern (можно несколько)")
    ap.add_argument("-p", "--pattern", action="append", help="паттерн из CLI")
    ap.add_argument("-o", "--output", default="ostrich_benchmarks_results.csv",
                    help="куда писать результаты CSV")
    ap.add_argument("--timeout", type=int, default=60, help="таймаут на прогон, с")
    ap.add_argument("--max-len", type=int, default=20,
                    help="верхняя граница длины переменных")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 1,
                    help="параллельных прогонов")
    ap.add_argument("--modes", default=",".join(MODES),
                    help="какие режимы прогонять, через запятую "
                         "(по умолчанию все: %s)" % ",".join(MODES))
    ap.add_argument("--baseline", action="store_true",
                    help="ключи без +commutation (базовый Ostrich)")
    ap.add_argument("--keep-smt", action="store_true",
                    help="не удалять сгенерированные .smt2")
    args = ap.parse_args()

    flags = runner.BASELINE_FLAGS if args.baseline else runner.COMMUTATION_FLAGS
    patterns = read_patterns(args)

    modes = [m.strip() for m in args.modes.split(",") if m.strip()]
    unknown = [m for m in modes if m not in MODES]
    if unknown:
        ap.error("неизвестные режимы: %s (доступны: %s)"
                 % (",".join(unknown), ",".join(MODES)))

    print("Решатель: %s" % runner.find_jar())
    print("Ключи:    %s" % " ".join(flags))
    print("Паттернов: %d   режимов: %d (%s)   таймаут: %ds   потоков: %d"
          % (len(patterns), len(modes), ",".join(modes), args.timeout, args.jobs))

    jobs = []
    for i, pat in enumerate(patterns, 1):
        for mode in modes:
            jobs.append((i, pat, mode))

    results = []
    done = 0
    total = len(jobs)

    # Инкрементальная запись: каждая готовая строка сразу пишется и сбрасывается
    # на диск, поэтому прерывание прогона не теряет уже посчитанные результаты.
    out_f = open(args.output, "w", newline="", encoding="utf-8")
    writer = csv.DictWriter(out_f, fieldnames=["pattern", "mode", "status",
                                               "time", "counter_example"])
    writer.writeheader()
    out_f.flush()

    def handle(r):
        nonlocal done
        done += 1
        results.append(r)
        writer.writerow(r)
        out_f.flush()
        print("[%4d/%d] %-12s %-12s -> %-8s  %.2fs  %s"
              % (done, total, r["pattern"], r["mode"], r["status"],
                 r["time"], r["counter_example"]), flush=True)

    try:
        if args.jobs > 1:
            with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
                futs = [ex.submit(check, idx, pat, mode, flags,
                                  args.timeout, args.max_len, args.keep_smt)
                        for (idx, pat, mode) in jobs]
                for fut in cf.as_completed(futs):
                    handle(fut.result())
        else:
            for idx, pat, mode in jobs:
                handle(check(idx, pat, mode, flags,
                             args.timeout, args.max_len, args.keep_smt))
    finally:
        out_f.close()

    print("\nРезультаты записаны в %s (строк: %d)" % (args.output, len(results)))

    sat = [r for r in results if r["status"] == "sat"]
    print("\nНайдено контрпримеров (sat): %d из %d" % (len(sat), len(results)))
    for r in sat[:5]:
        print("  %-12s %-12s  %s" % (r["pattern"], r["mode"], r["counter_example"]))

    print("\nСреднее время по режимам (с):")
    for mode in MODES:
        ts = [r["time"] for r in results if r["mode"] == mode]
        if ts:
            print("  %-12s %.3f" % (mode, sum(ts) / len(ts)))


if __name__ == "__main__":
    sys.exit(main())
