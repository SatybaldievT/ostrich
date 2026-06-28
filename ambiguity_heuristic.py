#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Эвристика доказательства (бесконечной) неоднозначности образцов.

Образец — строка над:
  * переменными (строчные буквы a..z),
  * константами  (заглавные буквы A..Z).

Морфизм sigma подставляет каждой переменной слово; константы остаются собой.
Образец НЕОДНОЗНАЧЕН, если существуют два РАЗНЫХ морфизма sigma != tau
с sigma(P) = tau(P).

Реализованы три части эвристики из постановки задачи:

  1) Балансирующие позиции.
     Позиция (разрез) делит образец на две части; если векторы кратностей
     переменных этих частей линейно зависимы (и оба ненулевые) — позиция
     балансирующая. Если разрез приходится точно вокруг константы (и слева,
     и справа от неё разрезы балансирующие) — говорим, что балансирующая
     позиция ЭТО БУКВА.

  2) Унарный критерий.
     Если балансирующая позиция — буква C, а кроме C во всём образце есть
     лишь переменные и ОДНА другая буква D, то неоднозначность доказывается
     словами-степенями буквы D. Формально: разрезаем образец по вхождениям
     C на сегменты; для совпадения слов достаточно, чтобы в каждом сегменте
     совпало суммарное число букв D. Заполняя переменные степенями D, это
     даёт линейную систему M*delta = 0 (M — матрица «сегмент x переменная»).
     Нетривиальное целочисленное ядро delta != 0 даёт пару sigma != tau.

  3) Бинарный критерий (плавные границы).
     Если унарный не сработал — ищем свидетеля над ДВУХБУКВЕННЫМ словом
     (конструктивный перебор присваиваний переменных короткими словами над
     {a,b}). Это реализует «плавные границы»: значения переменных — подслова
     одного периодического слова w^inf, и склейка кусков сохраняет слово.

ЛЮБОЙ выданный свидетель проверяется подстановкой, поэтому метка "proven"
означает строгое доказательство неоднозначности (без ложных срабатываний).
"""

import argparse
import csv
import functools
import itertools
import multiprocessing as mp
import os
import time

import sympy


# ---------------------------------------------------------------------------
# базовые операции над образцом
# ---------------------------------------------------------------------------
def variables(pattern):
    """Отсортированный список переменных (строчные буквы) образца."""
    return sorted(set(c for c in pattern if c.islower()))


def constants(pattern):
    """Множество констант (заглавные буквы) образца."""
    return set(c for c in pattern if c.isupper())


def var_vector(piece, vars_):
    """Вектор кратностей переменных в куске образца."""
    return [piece.count(v) for v in vars_]


def nonzero(vec):
    return any(x != 0 for x in vec)


def dependent(u, v):
    """Линейно зависимы ли два вектора одинаковой длины (оба ненулевые)."""
    if not nonzero(u) or not nonzero(v):
        return False
    # для двух векторов: зависимость <=> все 2x2-миноры равны нулю
    for i in range(len(u)):
        for j in range(i + 1, len(u)):
            if u[i] * v[j] - u[j] * v[i] != 0:
                return False
    return True


def substitute(pattern, assign):
    """Слово sigma(P): переменная -> значение, константа -> сама буква."""
    out = []
    for ch in pattern:
        if ch.islower():
            out.append(assign.get(ch, ""))
        else:
            out.append(ch)
    return "".join(out)


# ---------------------------------------------------------------------------
# 1) балансирующие позиции
# ---------------------------------------------------------------------------
def balancing_gaps(pattern):
    """Список разрезов i (1..n-1) с линейно зависимыми ненулевыми частями."""
    vars_ = variables(pattern)
    res = []
    for i in range(1, len(pattern)):
        l = var_vector(pattern[:i], vars_)
        r = var_vector(pattern[i:], vars_)
        if dependent(l, r):
            res.append(i)
    return res


def balancing_letters(pattern):
    """Список (index, letter): константа, вокруг которой обе части зависимы."""
    vars_ = variables(pattern)
    res = []
    for i, ch in enumerate(pattern):
        if not ch.isupper():
            continue
        l = var_vector(pattern[:i], vars_)
        r = var_vector(pattern[i + 1:], vars_)
        if dependent(l, r):
            res.append((i, ch))
    return res


def describe_balancing(pattern):
    """Человеко-читаемое описание балансирующих позиций."""
    letters = balancing_letters(pattern)
    gaps = balancing_gaps(pattern)
    parts = []
    if letters:
        parts.append("буквы " + ",".join("%s@%d" % (c, i) for i, c in letters))
    if gaps:
        parts.append("разрезы " + ",".join(str(i) for i in gaps))
    return "; ".join(parts) if parts else "нет"


# ---------------------------------------------------------------------------
# 2) унарный критерий
# ---------------------------------------------------------------------------
def integer_kernel_vector(rows, ncols):
    """Нетривиальный целочисленный вектор ядра матрицы rows (или None)."""
    if ncols == 0:
        return None
    M = sympy.Matrix(rows) if rows else sympy.zeros(1, ncols)
    ns = M.nullspace()
    if not ns:
        return None
    v = ns[0]
    # привести к целым: умножить на НОК знаменателей
    denoms = [sympy.nsimplify(x).q for x in v]
    lcm = 1
    for d in denoms:
        lcm = sympy.ilcm(lcm, d)
    iv = [int(x * lcm) for x in v]
    g = 0
    for x in iv:
        g = sympy.igcd(g, x)
    if g:
        iv = [x // g for x in iv]
    return iv if any(iv) else None


def unary_criterion(pattern):
    """Доказать неоднозначность унарными словами. Вернуть свидетеля или None."""
    consts = constants(pattern)
    vars_ = variables(pattern)
    if not vars_:
        return None
    for C in sorted(consts):
        others = consts - {C}
        if len(others) > 1:
            continue                     # нужна ровно одна «другая буква»
        D = next(iter(others)) if others else "#"   # буква-заполнитель
        # сегменты между вхождениями якоря C
        segments = pattern.split(C)
        rows = [var_vector(seg, vars_) for seg in segments]
        delta = integer_kernel_vector(rows, len(vars_))
        if delta is None:
            continue
        # base[v] = max(1, 1-delta[v]) -> оба присваивания >= 1 (без eps);
        # ядро гарантирует равенство слов при любом base.
        base = [max(1, 1 - d) for d in delta]
        k = [base[i] + delta[i] for i in range(len(vars_))]
        kp = base[:]
        sigma = {v: D * k[i] for i, v in enumerate(vars_)}
        tau = {v: D * kp[i] for i, v in enumerate(vars_)}
        if sigma == tau:
            continue
        if substitute(pattern, sigma) == substitute(pattern, tau):
            return {
                "kind": "unary",
                "anchor": C,
                "fill": D,
                "sigma": sigma,
                "tau": tau,
                "word": substitute(pattern, sigma),
            }
    return None


# ---------------------------------------------------------------------------
# 3) бинарный критерий — конструктивный поиск свидетеля над {a,b}
# ---------------------------------------------------------------------------
def words_upto(maxlen, alphabet, minlen=1):
    """Слова над alphabet длиной от minlen до maxlen (minlen=1 => без eps)."""
    if minlen == 0:
        yield ""
    for n in range(max(1, minlen), maxlen + 1):
        for tup in itertools.product(alphabet, repeat=n):
            yield "".join(tup)


def adaptive_maxlen(alphabet_size):
    """Глубина перебора, подобранная под размер алфавита (баланс полноты/скорости)."""
    if alphabet_size <= 2:
        return 9
    if alphabet_size == 3:
        return 6
    return 5


def binary_witness(pattern, maxlen=None):
    """Найти sigma != tau с совпадающими образами (или None).

    Значения переменных перебираются над АЛФАВИТОМ КОНСТАНТ образца — именно
    так устроена SMT-постановка (regex-ограничение str.in_re по алфавиту
    литералов). Поэтому буква-константа внутри переменной может «слиться» с
    литералом образца и сдвинуть якоря — за счёт этого и возникает коллизия.
    Если maxlen не задан — выбирается адаптивно по размеру алфавита.
    """
    vars_ = variables(pattern)
    if not vars_:
        return None
    alphabet = sorted(constants(pattern))
    if not alphabet:
        return None
    if maxlen is None:
        maxlen = adaptive_maxlen(len(alphabet))
    seen = {}                       # слово-образ -> присваивание
    pool = list(words_upto(maxlen, alphabet))
    for combo in itertools.product(pool, repeat=len(vars_)):
        assign = dict(zip(vars_, combo))
        w = substitute(pattern, assign)
        if w in seen and seen[w] != assign:
            sigma, tau = seen[w], assign
            return {
                "kind": "binary",
                "sigma": sigma,
                "tau": tau,
                "word": w,
            }
        seen.setdefault(w, assign)
    return None


# ---------------------------------------------------------------------------
# 3') критерий плавных границ — конструктивный свидетель над w = c1c2
# ---------------------------------------------------------------------------
def _factor_at_phase(c1, c2, phase, length):
    """Префикс слова w^inf (w=c1c2), стартующего с фазы phase, длины length.

    Фаза 0 -> c1 c2 c1 c2 ...,  фаза 1 -> c2 c1 c2 c1 ...
    """
    return "".join(c1 if (phase + i) % 2 == 0 else c2 for i in range(length))


def _solve_gf2(equations, n):
    """Решить линейную систему над GF(2).

    Каждое уравнение — битовая маска: биты 0..n-1 — коэффициенты при
    переменных b_x, бит n — правая часть. Возвращает частное решение
    b[0..n-1] (свободные переменные = 0) или None при несовместности.
    """
    pivots = {}                      # ведущий столбец -> приведённая строка
    for r in equations:
        cur = r
        while True:
            var_part = cur & ((1 << n) - 1)
            if var_part == 0:
                if (cur >> n) & 1:
                    return None       # 0 = 1 — система несовместна
                break                 # 0 = 0 — лишнее уравнение
            col = (var_part & -var_part).bit_length() - 1   # младший бит
            if col in pivots:
                cur ^= pivots[col]
            else:
                pivots[col] = cur
                break
    b = [0] * n
    for col in sorted(pivots, reverse=True):
        row = pivots[col]
        val = (row >> n) & 1
        for other in range(n):
            if other != col and (row >> other) & 1:
                val ^= b[other]
        b[col] = val
    return b


def smooth_boundary_witness(pattern):
    """Свидетель неоднозначности через ПЛАВНЫЕ ГРАНИЦЫ (период w = c1c2).

    Конструкция: подобрать двухбуквенное периодическое слово w=c1c2 так, чтобы
    образ sigma(P) был префиксом w^inf. Тогда значение каждой переменной —
    фактор w^inf, а каждая константа образца обязана стоять на «своей» позиции
    периода. Требование «фактор продолжает период» на каждой границе — это и
    есть плавность границы; для w=c1c2 оно сводится к линейной системе над
    GF(2) на ЧЁТНОСТИ длин переменных:

      * фаза перед символом = (число констант + сумма длин переменных слева)
        по модулю 2 — линейна по чётностям b_x;
      * константа A фиксирует фазу перед собой (0, если A=c1, иначе 1);
      * все вхождения одной переменной должны иметь равную входную фазу
        (иначе её значение-фактор не определено однозначно).

    При совместной системе ЛЮБЫЕ длины правильной чётности дают один и тот же
    образ-префикс. Перераспределяя длину между двумя переменными (одной +2,
    другой -2) при неизменной суммарной длине, получаем sigma != tau с равными
    образами. Свидетель проверяется подстановкой, поэтому ложных срабатываний
    нет.
    """
    vars_ = variables(pattern)
    if len(vars_) < 2:
        return None                  # нужна свобода перераспределить длину
    consts = constants(pattern)
    if len(consts) > 2:
        return None                  # двухбуквенное w не покроет 3+ констант
    var_idx = {v: i for i, v in enumerate(vars_)}
    n = len(vars_)

    # буквы-кандидаты для периода: константы образца + свежие буквы до двух штук
    letters = sorted(consts)
    for ch in (chr(c) for c in range(ord("A"), ord("Z") + 1)):
        if len(letters) >= 2:
            break
        if ch not in letters:
            letters.append(ch)

    pairs = [(c1, c2) for c1 in letters for c2 in letters
             if c1 != c2 and consts <= {c1, c2}]

    for c1, c2 in pairs:
        # символический проход: phase — маска чётности фазы ПЕРЕД текущим символом
        # (биты 0..n-1: коэф. при b_x, бит n: свободный член).
        phase = 0
        equations = []
        first_phase = {}             # var -> маска фазы при первом вхождении
        for ch in pattern:
            if ch.islower():
                i = var_idx[ch]
                if ch in first_phase:
                    equations.append(phase ^ first_phase[ch])  # фазы вхождений равны
                else:
                    first_phase[ch] = phase
                phase ^= (1 << i)              # длина переменной => сдвиг на b_x
            else:
                required = 0 if ch == c1 else 1
                equations.append(phase ^ (required << n))      # фаза = required
                phase ^= (1 << n)             # длина константы = 1

        b = _solve_gf2(equations, n)
        if b is None:
            continue                 # система несовместна — пробуем другой период

        # входная фаза каждой переменной при её (любом) вхождении
        phi = {}
        for v, mask in first_phase.items():
            val = (mask >> n) & 1
            for i in range(n):
                if (mask >> i) & 1:
                    val ^= b[i]
            phi[v] = val

        # перераспределение длины между двумя переменными так, чтобы ДЛИНА
        # ОБРАЗА не изменилась: переменная встречается count раз, поэтому
        # +2*count(v2) одной и -2*count(v1) другой компенсируют друг друга
        # (cnt[v1]*d1 - cnt[v2]*d2 = 0), а сдвиги чётные => чётности сохранены.
        cnt = {v: pattern.count(v) for v in vars_}
        v1, v2 = vars_[0], vars_[1]
        d1 = 2 * cnt[v2]
        d2 = 2 * cnt[v1]
        # запас в базовой длине, чтобы v2 после -d2 осталась >= 2
        base_len = {v: b[var_idx[v]] + d2 + 2 for v in vars_}
        len_sigma = dict(base_len)
        len_tau = dict(base_len)
        len_tau[v1] += d1
        len_tau[v2] -= d2

        sigma = {v: _factor_at_phase(c1, c2, phi[v], len_sigma[v]) for v in vars_}
        tau = {v: _factor_at_phase(c1, c2, phi[v], len_tau[v]) for v in vars_}
        if sigma == tau:
            continue
        if substitute(pattern, sigma) == substitute(pattern, tau):
            return {
                "kind": "smooth",
                "period": c1 + c2,
                "sigma": sigma,
                "tau": tau,
                "word": substitute(pattern, sigma),
            }
    return None


# ---------------------------------------------------------------------------
# классификация одного образца
# ---------------------------------------------------------------------------
def analyse(pattern, binary_maxlen=None):
    res = {
        "pattern": pattern,
        "balancing": describe_balancing(pattern),
        "verdict": "",
        "criterion": "",
        "witness": "",
        "word": "",
        "verified": "",
    }
    w = unary_criterion(pattern)
    crit = "unary"
    if w is None:
        w = smooth_boundary_witness(pattern)
        crit = "smooth"
    if w is None:
        w = binary_witness(pattern, maxlen=binary_maxlen)
        crit = "binary"
    if w is None:
        res["verdict"] = "не доказано"
        res["criterion"] = "-"
        return res

    ok = substitute(pattern, w["sigma"]) == substitute(pattern, w["tau"]) \
        and w["sigma"] != w["tau"]
    res["verdict"] = "НЕОДНОЗНАЧЕН" if ok else "ошибка свидетеля"
    res["criterion"] = crit
    res["verified"] = str(ok)
    res["witness"] = "sigma=%s | tau=%s" % (
        fmt_assign(w["sigma"]), fmt_assign(w["tau"]))
    res["word"] = w["word"]
    return res


def fmt_assign(assign):
    return "{" + ", ".join("%s=%s" % (k, (v or "eps"))
                           for k, v in sorted(assign.items())) + "}"


# ---------------------------------------------------------------------------
# бенчмарк
# ---------------------------------------------------------------------------
def analyse_with_timing(pattern, binary_maxlen=None):
    """Analyse pattern and record timing for each criterion."""
    res = {
        "pattern": pattern,
        "balancing": describe_balancing(pattern),
        "verdict": "",
        "criterion": "",
        "witness": "",
        "word": "",
        "verified": "",
        "time_unary_ms": 0.0,
        "time_smooth_ms": 0.0,
        "time_binary_ms": 0.0,
        "time_total_ms": 0.0,
    }

    start = time.perf_counter()

    t0 = time.perf_counter()
    w = unary_criterion(pattern)
    res["time_unary_ms"] = (time.perf_counter() - t0) * 1000.0
    crit = "unary"

    if w is None:
        t0 = time.perf_counter()
        w = smooth_boundary_witness(pattern)
        res["time_smooth_ms"] = (time.perf_counter() - t0) * 1000.0
        crit = "smooth"

    if w is None:
        t0 = time.perf_counter()
        w = binary_witness(pattern, maxlen=binary_maxlen)
        res["time_binary_ms"] = (time.perf_counter() - t0) * 1000.0
        crit = "binary"

    res["time_total_ms"] = (time.perf_counter() - start) * 1000.0

    if w is None:
        res["verdict"] = "не доказано"
        res["criterion"] = "-"
        return res

    ok = substitute(pattern, w["sigma"]) == substitute(pattern, w["tau"]) \
        and w["sigma"] != w["tau"]
    res["verdict"] = "НЕОДНОЗНАЧЕН" if ok else "ошибка свидетеля"
    res["criterion"] = crit
    res["verified"] = str(ok)
    res["witness"] = "sigma=%s | tau=%s" % (
        fmt_assign(w["sigma"]), fmt_assign(w["tau"]))
    res["word"] = w["word"]
    return res


def benchmark_patterns(patterns, binary_maxlen=None):
    """Run analysis with timing and print statistics."""
    print("\n" + "="*80)
    print("БЕНЧМАРК: Анализ образцов с измерением времени")
    print("="*80 + "\n")

    rows = []
    times_unary = []
    times_smooth = []
    times_binary = []
    times_total = []
    n_unary = n_smooth = n_binary = n_none = 0

    for p in patterns:
        r = analyse_with_timing(p, binary_maxlen=binary_maxlen)
        rows.append(r)

        if r["criterion"] == "unary":
            n_unary += 1
            times_unary.append(r["time_unary_ms"])
        elif r["criterion"] == "smooth":
            n_smooth += 1
            times_smooth.append(r["time_smooth_ms"])
        elif r["criterion"] == "binary":
            n_binary += 1
            times_binary.append(r["time_binary_ms"])
        else:
            n_none += 1

        times_total.append(r["time_total_ms"])

        # Detailed timing output
        timing_str = (f"(unary: {r['time_unary_ms']:.3f}ms, "
                      f"smooth: {r['time_smooth_ms']:.3f}ms, "
                      f"binary: {r['time_binary_ms']:.3f}ms, "
                      f"total: {r['time_total_ms']:.3f}ms)")
        print(f"{r['pattern']:12s} {r['verdict']:11s} {r['criterion']:7s}  {timing_str}")

    print("\n" + "="*80)
    print("СТАТИСТИКА ВРЕМЕНИ")
    print("="*80)
    print(f"Всего образцов:                  {len(patterns)}")
    print(f"  доказано унарным критерием:    {n_unary}")
    print(f"  доказано плавными границами:   {n_smooth}")
    print(f"  доказано бинарным критерием:   {n_binary}")
    print(f"  не доказано:                   {n_none}")

    print(f"\nОбщее время (total):")
    if times_total:
        print(f"  сумма:      {sum(times_total):>10.3f} ms")
        print(f"  среднее:    {sum(times_total) / len(times_total):>10.3f} ms")
        print(f"  мин/макс:   {min(times_total):>10.3f} / {max(times_total):>10.3f} ms")

    if times_unary:
        print(f"\nУнарный критерий ({len(times_unary)} patterns):")
        print(f"  сумма:      {sum(times_unary):>10.3f} ms")
        print(f"  среднее:    {sum(times_unary) / len(times_unary):>10.3f} ms")
        print(f"  мин/макс:   {min(times_unary):>10.3f} / {max(times_unary):>10.3f} ms")

    if times_smooth:
        print(f"\nПлавные границы ({len(times_smooth)} patterns):")
        print(f"  сумма:      {sum(times_smooth):>10.3f} ms")
        print(f"  среднее:    {sum(times_smooth) / len(times_smooth):>10.3f} ms")
        print(f"  мин/макс:   {min(times_smooth):>10.3f} / {max(times_smooth):>10.3f} ms")

    if times_binary:
        print(f"\nБинарный критерий ({len(times_binary)} patterns):")
        print(f"  сумма:      {sum(times_binary):>10.3f} ms")
        print(f"  среднее:    {sum(times_binary) / len(times_binary):>10.3f} ms")
        print(f"  мин/макс:   {min(times_binary):>10.3f} / {max(times_binary):>10.3f} ms")

    return rows


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def read_patterns(path):
    pats = []
    with open(path, newline="", encoding="utf-8") as f:
        r = csv.reader(f)
        header = next(r, None)
        for row in r:
            if not row:
                continue
            cell = row[0].strip()
            if cell:
                pats.append(cell)
    return pats


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description="Эвристика неоднозначности образцов")
    ap.add_argument("-i", "--input", default=os.path.join(here, "patterns_in.csv"))
    ap.add_argument("-o", "--output",
                    default=os.path.join(here, "ambiguity_heuristic_results.csv"))
    ap.add_argument("--binary-maxlen", type=int, default=None,
                    help="глубина бинарного перебора (по умолчанию адаптивно)")
    ap.add_argument("--benchmark", action="store_true",
                    help="добавить столбцы со временем выполнения по критериям")
    ap.add_argument("-j", "--workers", type=int, default=6,
                    help="число параллельных воркеров (по умолчанию 6)")
    ap.add_argument("patterns", nargs="*", help="образцы напрямую (вместо файла)")
    args = ap.parse_args()

    pats = args.patterns if args.patterns else read_patterns(args.input)

    fields = ["pattern", "balancing", "verdict", "criterion",
              "witness", "word", "verified"]
    if args.benchmark:
        fields.extend(["time_unary_ms", "time_smooth_ms",
                       "time_binary_ms", "time_total_ms"])

    # рабочая функция (выбирается по флагу benchmark); partial — picklable
    fn = analyse_with_timing if args.benchmark else analyse
    worker = functools.partial(fn, binary_maxlen=args.binary_maxlen)

    workers = max(1, args.workers)
    n_unary = n_smooth = n_binary = n_none = n_bad = 0
    total = len(pats)
    # накопители времени для бенчмарка (заполняются только при --benchmark)
    times_unary, times_smooth, times_binary, times_total = [], [], [], []

    # CSV открыт всё время работы: каждая готовая строка пишется и сбрасывается
    # на диск немедленно (imap_unordered -> по мере готовности, порядок свободный;
    # каждая строка самодостаточна — содержит свой pattern).
    with open(args.output, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        f.flush()

        def consume(iterable):
            nonlocal n_unary, n_smooth, n_binary, n_none, n_bad
            for i, r in enumerate(iterable, 1):
                w.writerow({k: r.get(k, "") for k in fields})
                f.flush()
                if r["criterion"] == "unary":
                    n_unary += 1
                elif r["criterion"] == "smooth":
                    n_smooth += 1
                elif r["criterion"] == "binary":
                    n_binary += 1
                else:
                    n_none += 1
                if r["verified"] == "False":
                    n_bad += 1
                if args.benchmark:
                    times_total.append(r.get("time_total_ms", 0.0))
                    if r["criterion"] == "unary":
                        times_unary.append(r.get("time_unary_ms", 0.0))
                    elif r["criterion"] == "smooth":
                        times_smooth.append(r.get("time_smooth_ms", 0.0))
                    elif r["criterion"] == "binary":
                        times_binary.append(r.get("time_binary_ms", 0.0))
                    print("[%d/%d] %-12s %-11s %-7s  total: %.3f ms" %
                          (i, total, r["pattern"], r["verdict"],
                           r["criterion"], r.get("time_total_ms", 0.0)),
                          flush=True)
                else:
                    print("[%d/%d] %-12s %-11s %-7s  %s" %
                          (i, total, r["pattern"], r["verdict"],
                           r["criterion"], r["witness"]), flush=True)

        if workers == 1:
            consume(worker(p) for p in pats)
        else:
            with mp.Pool(processes=workers) as pool:
                consume(pool.imap_unordered(worker, pats))

    print("\n===== ИТОГ =====")
    print("  воркеров:                       %d" % workers)
    print("  всего образцов:                 %d" % total)
    print("  доказано УНАРНЫМ критерием:     %d" % n_unary)
    print("  доказано ПЛАВНЫМИ границами:    %d" % n_smooth)
    print("  доказано БИНАРНЫМ критерием:    %d" % n_binary)
    print("  не доказано (в пределах поиска):%d" % n_none)
    print("  свидетелей не прошло проверку:  %d" % n_bad)

    if args.benchmark:
        def stat(name, xs):
            if not xs:
                return
            print("\n%s (%d):" % (name, len(xs)))
            print("  сумма:      %10.3f ms" % sum(xs))
            print("  среднее:    %10.3f ms" % (sum(xs) / len(xs)))
            print("  мин/макс:   %10.3f / %10.3f ms" % (min(xs), max(xs)))

        print("\n" + "=" * 60)
        print("СТАТИСТИКА ВРЕМЕНИ")
        print("=" * 60)
        stat("Общее время (total)", times_total)
        stat("Унарный критерий", times_unary)
        stat("Плавные границы", times_smooth)
        stat("Бинарный критерий", times_binary)

    print("\nЗаписано -> %s" % args.output)
    return 1 if n_bad else 0


if __name__ == "__main__":
    mp.freeze_support()
    raise SystemExit(main())
