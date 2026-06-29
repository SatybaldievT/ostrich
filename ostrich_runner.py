#!/usr/bin/env python3
"""
Общий модуль запуска решателя Ostrich из Python.

Находит собранный jar, запускает решатель на .smt2 файле с заданным набором
ключей и возвращает результат: статус (sat/unsat/unknown), stdout, stderr (логи),
время работы.

Ключ курсовой: +commutation  (включает commutation-class splitting/normalization).
Без ключа решатель ведёт себя как базовый Ostrich.

Используется скриптами check_tests.py и run_coursework.py.
"""

import glob
import os
import re
import subprocess
import sys
import time

BASEDIR = os.path.dirname(os.path.abspath(__file__))
MAIN_CLASS = "ostrich.OstrichMain"
DEFAULT_SOLVER = "ostrich.OstrichStringTheory"
JAVA_OPTS = ["-Xss40000k", "-Xmx2000m"]

# Базовый набор ключей (профиль Ostrich по умолчанию), без курсовой надстройки
BASELINE_FLAGS = ["+backwardPropagation", "+nielsenSplitter"]
# Тот же набор, но с включённой курсовой функциональностью (ваш ключ)
COMMUTATION_FLAGS = BASELINE_FLAGS + ["+commutation"]


def find_jar():
    """Найти собранный assembly jar (самый свежий)."""
    pattern = os.path.join(BASEDIR, "target", "scala-*", "ostrich-assembly*.jar")
    jars = glob.glob(pattern)
    if not jars:
        raise FileNotFoundError(
            "Не найден ostrich-assembly*.jar в target/scala-*/.\n"
            "Соберите решатель:  java -jar sbt-launch.jar assembly")
    return max(jars, key=os.path.getmtime)


STATUS_RE = re.compile(r"^\s*(sat|unsat|unknown)\s*$", re.MULTILINE)


def parse_status(stdout: str):
    """Извлечь итоговый статус (последнее sat/unsat/unknown в stdout)."""
    matches = STATUS_RE.findall(stdout)
    return matches[-1] if matches else None


def run(smt_file, flags=None, solver=DEFAULT_SOLVER, timeout=60, java="java",
        extra_args=None):
    """
    Запустить Ostrich на файле.

    flags       : ключи решателя (идут в -stringSolver=...:flag1,flag2)
    extra_args  : общие ключи OstrichMain как отдельные аргументы
                  (например ["+incremental", "+model"] — нужны, чтобы
                  (get-model) выдавал модель).

    Возвращает dict:
        status     : 'sat' | 'unsat' | 'unknown' | None
        stdout     : str  (включая модель из (get-model))
        stderr     : str  (логи решателя, включая [commutation]-вывод)
        time       : секунды
        timeout    : bool
        returncode : int | None
        cmd        : list[str]
    """
    if flags is None:
        flags = []
    if extra_args is None:
        extra_args = []
    jar = find_jar()
    flag_str = ",".join(flags)
    string_solver = "-stringSolver=" + solver + (":" + flag_str if flag_str else "")
    cmd = ([java] + JAVA_OPTS + ["-cp", jar, MAIN_CLASS, string_solver]
           + list(extra_args) + [smt_file])

    start = time.time()
    timed_out = False
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              encoding="utf-8", errors="replace", timeout=timeout)
        stdout, stderr, rc = proc.stdout, proc.stderr, proc.returncode
    except subprocess.TimeoutExpired as e:
        timed_out = True
        stdout = (e.stdout or b"")
        stderr = (e.stderr or b"")
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", "replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", "replace")
        rc = None
    elapsed = time.time() - start

    return {
        "status": None if timed_out else parse_status(stdout),
        "stdout": stdout,
        "stderr": stderr,
        "time": elapsed,
        "timeout": timed_out,
        "returncode": rc,
        "cmd": cmd,
    }


if __name__ == "__main__":
    # Ручной запуск: python ostrich_runner.py <file.smt2> [flags...]
    if len(sys.argv) < 2:
        print("usage: python ostrich_runner.py <file.smt2> [flags...]", file=sys.stderr)
        print("по умолчанию ключи:", COMMUTATION_FLAGS, file=sys.stderr)
        sys.exit(2)
    f = sys.argv[1]
    extra = sys.argv[2:] or COMMUTATION_FLAGS
    print("jar:", find_jar(), file=sys.stderr)
    res = run(f, flags=extra)
    print("=== STATUS: %s   time: %.2fs %s" %
          (res["status"], res["time"], "(TIMEOUT)" if res["timeout"] else ""),
          file=sys.stderr)
    print("--- stdout ---")
    sys.stdout.write(res["stdout"])
    print("--- stderr (логи) ---", file=sys.stderr)
    sys.stderr.write(res["stderr"])
