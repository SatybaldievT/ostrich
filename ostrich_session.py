#!/usr/bin/env python3
"""
Постоянная сессия Ostrich: одна JVM на много задач, без переинициализации.

Вместо запуска нового процесса `java ... OstrichMain file.smt2` на каждый пример
(дорогой старт JVM + сборка теории/портфолио + парсинг) мы держим ОДИН процесс в
инкрементальном режиме Princess и меняем только условия:

    java ... ostrich.OstrichMain -stringSolver=...:<flags> \
         +incremental +model +stdin -timeoutPer=<ms>

Перед каждой задачей шлём `(reset)`, затем новые объявления/ассерты,
`(check-sat)`, `(get-model)` и `(echo "<sentinel>")`, после чего читаем stdout до
маркера. Решатель инициализируется один раз; `-timeoutPer` ограничивает КАЖДЫЙ
запрос и возвращает `unknown`, НЕ убивая процесс (тёплая JVM сохраняется).

Класс OstrichSession — одна сессия (одна задача за раз). Для параллелизма
поднимайте несколько сессий (несколько JVM), это всё равно K инициализаций
вместо N. Демонстрация в __main__.
"""

import subprocess
import sys
import time

import ostrich_runner as runner
from ostrich_benchmarks import generate, parse_model, format_counter_example

SENTINEL = "<<OSTRICH-END>>"
_SENT_LINES = {SENTINEL, '"%s"' % SENTINEL}
_STATUS = {"sat", "unsat", "unknown"}


class OstrichSession:
    """Один долгоживущий процесс Ostrich в инкрементальном режиме."""

    def __init__(self, flags=None, timeout_ms=30000, jar=None, java="java"):
        self.jar = jar or runner.find_jar()
        flags = list(flags if flags is not None else runner.COMMUTATION_FLAGS)
        flag_str = ",".join(flags)
        solver = "-stringSolver=" + runner.DEFAULT_SOLVER + (
            ":" + flag_str if flag_str else "")
        self.cmd = ([java] + runner.JAVA_OPTS
                    + ["-cp", self.jar, runner.MAIN_CLASS, solver,
                       "+incremental", "+model", "+stdin",
                       "-timeoutPer=%d" % int(timeout_ms)])
        self.proc = subprocess.Popen(
            self.cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, text=True,
            encoding="utf-8", errors="replace", bufsize=1)

    def solve_smt(self, problem_smt):
        """
        Прогнать самодостаточный SMT-блок (с (set-logic ...), (check-sat),
        опционально (get-model)). Вернуть (status, stdout_text, elapsed_sec).
        Между задачами шлём (reset) — состояние предыдущей очищается.
        """
        block = "(reset)\n" + problem_smt.rstrip() + \
                '\n(echo "%s")\n' % SENTINEL
        start = time.time()
        if self.proc.poll() is not None:
            return None, "", 0.0  # процесс умер
        self.proc.stdin.write(block)
        self.proc.stdin.flush()

        out, status = [], None
        while True:
            line = self.proc.stdout.readline()
            if line == "":          # EOF — процесс завершился
                break
            s = line.strip()
            if s in _SENT_LINES:
                break
            out.append(line)
            if status is None and s in _STATUS:
                status = s
        return status, "".join(out), time.time() - start

    def alive(self):
        return self.proc.poll() is None

    def close(self):
        try:
            if self.proc.poll() is None:
                self.proc.stdin.write("(exit)\n")
                self.proc.stdin.flush()
                self.proc.wait(timeout=5)
        except Exception:
            pass
        finally:
            if self.proc.poll() is None:
                self.proc.kill()


def solve_pattern(session, pattern, mode="base", max_len=20):
    """Решить один паттерн в данной сессии; вернуть dict как в бенчмарке."""
    smt, variables = generate(pattern, mode, max_len)
    if smt is None:
        return {"pattern": pattern, "mode": mode, "status": "unique",
                "time": 0.0, "counter_example": ""}
    status, out, elapsed = session.solve_smt(smt)
    status = status or "unknown"
    counter = ""
    if status == "sat":
        counter = format_counter_example(parse_model(out), variables)
    return {"pattern": pattern, "mode": mode, "status": status,
            "time": elapsed, "counter_example": counter}


def _read_csv_patterns(path):
    import csv
    pats = []
    with open(path, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            p = (row.get("pattern") or "").strip()
            if p:
                pats.append(p)
    return pats


if __name__ == "__main__":
    import argparse
    import csv

    ap = argparse.ArgumentParser(
        description="Прогон паттернов в постоянной сессии Ostrich (одна JVM)")
    ap.add_argument("patterns", nargs="*", help="паттерны прямо в CLI")
    ap.add_argument("--csv", help="CSV с колонкой pattern")
    ap.add_argument("-o", "--output", default="ostrich_session_results.csv",
                    help="куда писать результаты")
    ap.add_argument("--mode", default="base", help="режим (base/...)")
    ap.add_argument("--timeout", type=int, default=30, help="таймаут на запрос, с")
    ap.add_argument("--recycle", type=int, default=25,
                    help="пересоздавать сессию каждые N примеров (0 — никогда)")
    args = ap.parse_args()

    if args.csv:
        pats = _read_csv_patterns(args.csv)
    elif args.patterns:
        pats = args.patterns
    else:
        pats = ["xxAyyByx", "xyAxBxyy", "xAyBxyxy", "xxAyyBxy"]

    tmo_ms = args.timeout * 1000
    print("Паттернов: %d   режим: %s   таймаут/запрос: %ds   пересоздание: %s"
          % (len(pats), args.mode, args.timeout,
             ("каждые %d" % args.recycle) if args.recycle else "никогда"))

    out_f = open(args.output, "w", newline="", encoding="utf-8")
    w = csv.DictWriter(out_f, fieldnames=["pattern", "mode", "status",
                                          "time", "counter_example"])
    w.writeheader()
    out_f.flush()

    t0 = time.time()
    sess = OstrichSession(timeout_ms=tmo_ms)
    inits = 1
    try:
        for i, pat in enumerate(pats, 1):
            if args.recycle and i > 1 and (i - 1) % args.recycle == 0:
                sess.close()
                sess = OstrichSession(timeout_ms=tmo_ms)
                inits += 1
            if not sess.alive():
                sess = OstrichSession(timeout_ms=tmo_ms)
                inits += 1
            r = solve_pattern(sess, pat, args.mode)
            w.writerow(r)
            out_f.flush()
            print("  [%3d/%d] %-12s -> %-8s %6.2fs  %s"
                  % (i, len(pats), r["pattern"], r["status"], r["time"],
                     r["counter_example"]), flush=True)
    finally:
        sess.close()
        out_f.close()

    print("Итого: %.2fs   инициализаций JVM: %d (вместо %d при per-file)"
          % (time.time() - t0, inits, len(pats)))
