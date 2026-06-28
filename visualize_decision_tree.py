#!/usr/bin/env python3
"""
Visualizer for the OSTRICH Nielsen-splitter decision tree.

Reads the JSON produced by OstrichNielsenSplitter.DecisionTreeLogger
(decision_tree.json by default) and renders, for every decision, the
state transition it performs:

        FROM   (the word equation the rule is applied to)
          |    rule + parameters
          v
        TO     (the resulting equation(s) / branch alternatives)

Output:
  * a colored transition view in the terminal (always);
  * a self-contained interactive HTML file (decision_tree.html);
  * a Graphviz "derivation flow" graph (decision_tree.dot, rendered to
    .svg/.png if the `dot` executable is available): state notes feed
    into decision nodes which yield the next state(s), and decisions are
    chained in proof order.

Usage:
    python visualize_decision_tree.py [decision_tree.json] [--no-html] [--dot]
"""

import argparse
import html
import json
import os
import shutil
import subprocess
import sys

# label, ANSI color, hex color
RULE_STYLE = {
    "nielsenCommutationSplit":  ("Commutation split",                 "95", "#8e44ad"),
    "splitEquationWithLenNorm": ("Comm-class normalization",          "36", "#16a085"),
    "splitEquationWithLen":     ("Nielsen split",                     "33", "#d35400"),
    "decompEquation":           ("Nielsen decomp (a.b=c.d)",          "34", "#2980b9"),
    "decompSimpleEquation":     ("Nielsen decomp (a.b=word)",         "32", "#27ae60"),
}
DEFAULT_STYLE = ("decision", "37", "#555555")

# Rules whose action is a real case split (OR-branching) rather than a
# linear rewrite (AND / single continuation).
SPLIT_RULES = {"nielsenCommutationSplit", "splitEquationWithLen"}

# --- output encoding (Windows legacy code pages can't do box drawing) -------
try:
    sys.stdout.reconfigure(encoding="utf-8")
    _U = True
except Exception:
    _U = False
ARROW = "│\n▼" if _U else "|\nv"
DOWN = "▼" if _U else "v"


def style_for(node):
    return RULE_STYLE.get(node.get("rule", ""), DEFAULT_STYLE)


def c(text, color):
    if not sys.stdout.isatty():
        return text
    return "\033[%sm%s\033[0m" % (color, text)


def vis(s):
    """Make control / non-printable characters visible as \\xNN."""
    out = []
    for ch in str(s):
        o = ord(ch)
        out.append("\\x%02x" % o if o < 0x20 or o == 0x7f else ch)
    return "".join(out)


# ---------------------------------------------------------------------------
# Map each node to a (from_state, [to_states], params) transition.
# ---------------------------------------------------------------------------
def _lhs(eq_lit):
    """'a . b = res'  ->  'a . b'  (drop the shared result term)."""
    return eq_lit.split(" = ")[0].strip()


def transition(node):
    rule = node.get("rule", "")

    # explicit before/after pair (normalization)
    if "before" in node and "after" in node:
        frm, to = node["before"], [node["after"]]
    elif rule in ("decompEquation", "decompSimpleEquation",
                  "nielsenCommutationSplit"):
        frm, to = node.get("equation", ""), node.get("branches", [])
    elif rule == "splitEquationWithLen":
        if "lit1" in node and "lit2" in node:
            frm = _lhs(node["lit1"]) + " == " + _lhs(node["lit2"])
        else:
            frm = "split on " + node.get("symbol", "?")
        to = node.get("branches", [])
    else:
        frm = node.get("equation", node.get("before", ""))
        to = node.get("branches",
                      [node["after"]] if "after" in node else [])

    # compact parameter string for the decision label
    parts = []
    for k in ("x1", "x2", "J", "J1", "splitSym", "symbol", "splitLen",
              "commutationClass"):
        if k in node:
            v = node[k]
            v = ", ".join(map(str, v)) if isinstance(v, list) else str(v)
            parts.append("%s=%s" % (k, v))
    return vis(frm), [vis(t) for t in to], "  ".join(parts)


# ---------------------------------------------------------------------------
# Terminal
# ---------------------------------------------------------------------------
def render_terminal(nodes):
    print(c("OSTRICH derivation flow", "1") + "  (%d decisions)\n" % len(nodes))
    for i, node in enumerate(nodes):
        label, color, _ = style_for(node)
        frm, to, params = transition(node)

        if i == 0:
            print("   " + c(frm if frm else "(initial equation)", "2"))
        # decision
        head = "[%d] %s" % (i + 1, label)
        print("   " + c(DOWN, color) + "  " + c(head, "1;" + color) +
              ("  " + c(params, "2") if params else ""))
        # resulting states
        is_split = node.get("rule", "") in SPLIT_RULES
        if to:
            for j, t in enumerate(to):
                if is_split:
                    tag = c(" (taken)", "1;32") if j == 0 else c(" (closed)", "31")
                else:
                    tag = ""
                print("       " + c("→", color) + " " + t + tag)
        else:
            print("       " + c("(no explicit result captured)", "2"))
        if i != len(nodes) - 1:
            print("   " + c("│", color))
    print()


# ---------------------------------------------------------------------------
# HTML
# ---------------------------------------------------------------------------
HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>OSTRICH derivation flow</title>
<style>
 body {{ font-family:-apple-system,Segoe UI,Roboto,sans-serif;
         background:#15151f; color:#e6e6e6; margin:0; padding:32px; }}
 h1 {{ font-size:20px; }}
 .sub {{ color:#9a9aae; margin-bottom:24px; }}
 .state {{ font-family:monospace; font-size:12px; background:#101019;
           border:1px solid #2c2c40; border-radius:6px; padding:8px 12px;
           white-space:pre-wrap; word-break:break-all; margin:0 0 0 6px; }}
 .state.init {{ border-color:#5a5a80; }}
 .flow {{ display:flex; align-items:stretch; margin:10px 0; }}
 .arrowcol {{ width:42px; display:flex; flex-direction:column;
              align-items:center; color:var(--c); }}
 .arrowcol .line {{ flex:1; width:2px; background:var(--c); }}
 .arrowcol .tip {{ font-size:16px; line-height:1; }}
 .decision {{ flex:1; background:#23233a; border-left:4px solid var(--c);
              border-radius:8px; padding:10px 14px; }}
 .decision h2 {{ margin:0; font-size:14px; }}
 .decision .rule {{ color:#9a9aae; font-family:monospace; font-size:11px; }}
 .decision .params {{ color:#c9c9e0; font-family:monospace; font-size:12px;
                      margin-top:4px; }}
 .badge {{ background:var(--c); color:#fff; border-radius:6px;
           padding:1px 8px; font-size:11px; margin-left:8px; }}
 .to {{ margin-top:8px; }}
 .to .lbl {{ color:#9a9aae; font-size:11px; }}
 .to ul {{ list-style:none; margin:4px 0 0; padding:0; }}
 .to li {{ font-family:monospace; font-size:12px; background:#101019;
           border-radius:6px; padding:5px 10px; margin:3px 0;
           border-left:3px solid var(--c); }}
 .to li::before {{ content:'→ '; color:var(--c); }}
 .to li.taken {{ border-left-color:#2ecc71; }}
 .to li.taken::after {{ content:' ✓ taken'; color:#2ecc71; font-size:10px; }}
 .to li.closed {{ border-left-color:#e74c3c; opacity:.7; }}
 .to li.closed::after {{ content:' ✗ closed'; color:#e74c3c; font-size:10px; }}
 .from {{ margin-top:8px; }}
 .from .lbl {{ color:#9a9aae; font-size:11px; }}
 .from .eq {{ font-family:monospace; font-size:12px; background:#101019;
              border-radius:6px; padding:6px 10px; margin-top:3px;
              white-space:pre-wrap; word-break:break-all;
              border-left:3px solid #5a5a80; }}
 .from .eq.before {{ border-left-color:#e67e22; }}
 .from .eq.after {{ border-left-color:#2ecc71; }}
 .from .eqarrow {{ color:#9a9aae; font-size:11px; margin:3px 0; }}
 .state {{ margin-top:8px; }}
 .state summary {{ color:#9a9aae; font-size:11px; cursor:pointer; }}
 .state ul {{ list-style:none; margin:4px 0 0; padding:0; }}
 .state li {{ font-family:monospace; font-size:12px; background:#0c0c14;
              border-radius:6px; padding:5px 10px; margin:3px 0;
              white-space:pre-wrap; word-break:break-all;
              border-left:3px solid #444; }}
</style></head><body>
<h1>OSTRICH Nielsen-splitter derivation flow</h1>
<div class="sub">{count} decisions &middot; source: {src} &middot;
  read top&rarr;bottom: each box transforms the equation above it</div>
<div class="state init">{init}</div>
{steps}
</body></html>
"""


def render_html(nodes, src, out_path):
    init = ""
    if nodes:
        f0, _, _ = transition(nodes[0])
        init = html.escape(f0) if f0 else "(initial equation)"

    blocks = []
    for i, node in enumerate(nodes):
        label, _, hexc = style_for(node)
        frm, to, params = transition(node)
        rule = html.escape(node.get("rule", ""))
        kind = html.escape(node.get("kind", ""))
        badge = '<span class="badge">%s</span>' % kind if kind else ""
        params_h = ('<div class="params">%s</div>' % html.escape(params)
                    if params else "")
        is_split = node.get("rule", "") in SPLIT_RULES
        is_norm = node.get("rule", "") == "splitEquationWithLenNorm"

        # the formula that participates, embedded in the node itself
        if is_norm:
            from_h = ('<div class="from"><span class="lbl">меняется:</span>'
                      '<div class="eq before">%s</div>'
                      '<div class="eqarrow">&#8595; нормализация</div>'
                      '<div class="eq after">%s</div></div>'
                      % (html.escape(vis(node.get("before", ""))),
                         html.escape(vis(node.get("after", "")))))
            yields_lbl = "результат (after)"
            to = []  # already shown as before/after
        else:
            from_h = ('<div class="from"><span class="lbl">участвует:</span>'
                      '<div class="eq">%s</div></div>' % html.escape(frm)
                      if frm else "")
            yields_lbl = "ветви (taken/closed)" if is_split \
                else "выводится (∧)"

        li = []
        for j, t in enumerate(to):
            cls = (" taken" if j == 0 else " closed") if is_split else ""
            li.append('<li class="r%s">%s</li>' % (cls, html.escape(t)))
        to_block = ('<div class="to"><span class="lbl">%s:</span><ul>%s</ul>'
                    '</div>' % (yields_lbl, "".join(li))) if li else ""

        # full set of equations present in the goal at this moment
        state = node.get("state", [])
        if state:
            si = "".join("<li>%s</li>" % html.escape(vis(s)) for s in state)
            state_h = ('<details class="state"><summary>все формулы подцели '
                       '(%d)</summary><ul>%s</ul></details>'
                       % (len(state), si))
        else:
            state_h = ""

        blocks.append(
            '<div class="flow" style="--c:%s">'
            '<div class="arrowcol"><div class="line"></div>'
            '<div class="tip">&#9660;</div><div class="line"></div></div>'
            '<div class="decision">'
            '<h2>[%d] %s%s</h2><div class="rule">%s</div>%s%s%s%s</div></div>'
            % (hexc, i + 1, html.escape(label), badge, rule,
               params_h, from_h, to_block, state_h))

    out = HTML_TEMPLATE.format(count=len(nodes), src=html.escape(src),
                               init=init, steps="\n".join(blocks))
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(out)
    print("Wrote %s" % out_path)


# ---------------------------------------------------------------------------
# Graphviz derivation-flow graph
# ---------------------------------------------------------------------------
def dot_esc(s):
    return (vis(s).replace("\\", "\\\\").replace('"', "'")
            .replace("\r", "").replace("\n", "\\n"))


def wrap(s, width=72):
    """Hard-wrap a long string onto multiple lines (no truncation)."""
    s = str(s)
    if len(s) <= width:
        return s
    return "\n".join(s[i:i + width] for i in range(0, len(s), width))


def render_dot(nodes, out_dot):
    """Render the realized derivation as a real TREE.

    Each decision is attached to its true parent decision via the explicit
    `parentSeq`/`branch` fields the logger now records (recovered from the
    nesting of order-constants).  So when the prover moves to a sibling branch,
    its decisions hang under the correct parent branch instead of being chained
    linearly.  For case splits, the alternatives in `to` that produced no logged
    child are drawn as dashed "closed/unlogged" leaf stubs.
    """
    L = ['digraph derivation {', '  rankdir=TB;', '  splines=true;',
         '  node [fontname="monospace" fontsize=9];',
         '  ranksep=0.35;']

    # index decisions by their seq and group children by parent
    by_seq = {}
    children = {}
    for i, node in enumerate(nodes):
        s = node.get("seq", i)
        by_seq[s] = node
        p = node.get("parentSeq", -1)
        children.setdefault(p, []).append(node)
    for v in children.values():
        v.sort(key=lambda n: n.get("branch", 0))

    # root = the initial equation
    f0 = transition(nodes[0])[0] if nodes else ""
    L.append('  root [shape=note fillcolor="#1b2230" style=filled '
             'fontcolor="#cfe0ff" label="%s"];' % dot_esc(wrap(f0)))

    # one decision box per node
    for i, node in enumerate(nodes):
        s = node.get("seq", i)
        label, _, hexc = style_for(node)
        frm, to, params = transition(node)
        rule = node.get("rule", "")
        is_norm = rule == "splitEquationWithLenNorm"
        dlines = ["[seq %d] %s" % (s, label)]
        if params:
            dlines.append(wrap(params))
        if is_norm:
            dlines.append("до:  " + wrap(node.get("before", "")))
            dlines.append("после: " + wrap(node.get("after", "")))
        elif frm:
            dlines.append("формула: " + wrap(frm))
        dlbl = "\\n".join(dot_esc(x) for x in dlines)
        L.append('  d%d [shape=box style="rounded,filled" fillcolor="%s" '
                 'fontcolor="white" label="%s"];' % (s, hexc, dlbl))

    # parent -> child edges (labeled with the branch index)
    for i, node in enumerate(nodes):
        s = node.get("seq", i)
        p = node.get("parentSeq", -1)
        br = node.get("branch", 0)
        if p < 0 or p not in by_seq:
            L.append('  root -> d%d [color="#777"];' % s)
        else:
            L.append('  d%d -> d%d [color="#777" label="%s"];'
                     % (p, s, dot_esc("ветка %d" % br)))

    # closed / unlogged alternatives of each split, as dashed leaf stubs
    for i, node in enumerate(nodes):
        rule = node.get("rule", "")
        if rule not in SPLIT_RULES:
            continue
        s = node.get("seq", i)
        _, to, _ = transition(node)
        explored = {c.get("branch", 0) for c in children.get(s, [])}
        for j, t in enumerate(to):
            if j in explored:
                continue
            cj = "stub%d_%d" % (s, j)
            L.append('  %s [shape=note fillcolor="#2a0e0e" style=filled '
                     'fontcolor="#f0bdbd" label="%s"];'
                     % (cj, dot_esc(wrap(t) + "  (закрыта / не лог.)")))
            L.append('  d%d -> %s [color="#a55" style=dashed label="%s"];'
                     % (s, cj, dot_esc("ветка %d" % j)))
    L.append('}')
    with open(out_dot, "w", encoding="utf-8") as f:
        f.write("\n".join(L))
    print("Wrote %s" % out_dot)

    dot = shutil.which("dot")
    if not dot:
        print("(graphviz 'dot' not found; render with: dot -Tsvg %s -o x.svg)"
              % out_dot)
        return
    for fmt in ("svg", "png"):
        out = out_dot.rsplit(".", 1)[0] + "." + fmt
        try:
            subprocess.run([dot, "-T" + fmt, out_dot, "-o", out], check=True)
            print("Rendered %s" % out)
        except subprocess.CalledProcessError as e:
            print("dot failed for %s: %s" % (fmt, e), file=sys.stderr)


# ---------------------------------------------------------------------------
# Full step-by-step textual report (Markdown)
# ---------------------------------------------------------------------------
RULE_EXPLAIN = {
    "nielsenCommutationSplit":
        "Коммутационный сплит: уравнение x^J·… = y^I·… порождает 3 случая — "
        "ветка коммутации (x·y=y·x, регистрируется класс) и две граничные "
        "(x выражается через степень y).",
    "splitEquationWithLen":
        "Стандартный сплит Нильсена: выбирается символ для разреза по модели "
        "длин; ветка align выравнивает префиксы, ветка diff-len отбрасывает "
        "несовместимые длины.",
    "splitEquationWithLenNorm":
        "Нормализация по классу коммутации: коммутирующие переменные "
        "переупорядочиваются в канонический вид (P·RL·U' == P·RR·V').",
    "decompEquation":
        "Декомпозиция a.b = c.d при выводимом равенстве длин |a|=|c|: "
        "уравнение разбивается на a=c и b=d.",
    "decompSimpleEquation":
        "Декомпозиция a.b = w (конкретное слово): слово делится по позиции, "
        "a и b приравниваются к префиксу и суффиксу w.",
}

ACTION_KIND = {  # how the formula changes
    "nielsenCommutationSplit": "ветвление (AxiomSplit, OR-случаи)",
    "splitEquationWithLen":    "ветвление (AxiomSplit, OR-случаи)",
    "splitEquationWithLenNorm":"перезапись (AddAxiom + RemoveFacts)",
    "decompEquation":          "перезапись на конъюнкцию (AddAxiom + RemoveFacts)",
    "decompSimpleEquation":    "перезапись на конъюнкцию (AddAxiom + RemoveFacts)",
}


def render_report(nodes, src, out_md):
    out = []
    w = out.append
    import collections
    cnt = collections.Counter(n.get("rule", "") for n in nodes)
    forks = sum(1 for n in nodes if n.get("rule", "") in SPLIT_RULES)

    w("# OSTRICH — полный вывод дерева решений\n")
    w("Источник: `%s`  ·  всего этапов: **%d**  ·  точек ветвления "
      "(AxiomSplit): **%d**\n" % (src, len(nodes), forks))
    w("\nСостав решений:")
    for r, n in cnt.items():
        lbl = RULE_STYLE.get(r, (r,))[0]
        w("- `%s` (%s): %d" % (r, lbl, n))
    if nodes:
        w("\n**Исходное уравнение:**\n")
        w("```\n%s\n```" % transition(nodes[0])[0])
    w("\n---\n")

    for i, node in enumerate(nodes):
        label = style_for(node)[0]
        rule = node.get("rule", "")
        frm, to, params = transition(node)
        is_split = rule in SPLIT_RULES
        gid = node.get("gid", "")
        seq = node.get("seq", i)

        w("## Этап %d — %s" % (i + 1, label))
        w("")
        w("- **правило:** `%s`  ·  *%s*" % (rule, node.get("kind", "")))
        w("- **подцель (gid):** `%s`  ·  **seq:** %s" % (gid, seq))
        w("- **тип изменения:** %s" % ACTION_KIND.get(rule, node.get("action", "")))
        if rule in RULE_EXPLAIN:
            w("- **смысл:** %s" % RULE_EXPLAIN[rule])
        if params:
            w("- **параметры:** `%s`" % params)
        w("")

        # which formula participates / how it changes
        if rule == "splitEquationWithLenNorm":
            w("**Участвует формула (до):**")
            w("```\n%s\n```" % vis(node.get("before", "")))
            w("**Становится (после нормализации):**")
            w("```\n%s\n```" % vis(node.get("after", "")))
        else:
            if frm:
                w("**Участвует формула:**")
                w("```\n%s\n```" % frm)
            if is_split:
                w("**Ветвление на случаи:**")
                for j, t in enumerate(to):
                    mark = "✅ **взята**" if j == 0 else "❌ закрыта"
                    w("- %s — %s" % (mark, t))
            else:
                w("**Выводится (конъюнкция равенств):**")
                for t in to:
                    w("- %s" % t)
        w("\n---\n")

    text = "\n".join(out)
    with open(out_md, "w", encoding="utf-8") as f:
        f.write(text)
    print("Wrote %s" % out_md)


# ---------------------------------------------------------------------------
def load_nodes(path):
    """Load the decision-tree nodes, tolerating a truncated tail.

    The logger rewrites the whole JSON after every node; if the solver is
    killed mid-write (e.g. OOM) the file ends in a half-written record, which
    breaks a strict json.load.  In that case we salvage every COMPLETE node
    object from the `decisionTree` array and stop at the truncated tail.
    """
    with open(path, encoding="utf-8") as f:
        txt = f.read()
    try:
        return json.loads(txt).get("decisionTree", [])
    except json.JSONDecodeError:
        pass
    key = txt.find('"decisionTree"')
    start = txt.find('[', key) if key >= 0 else -1
    if start < 0:
        raise
    dec = json.JSONDecoder()
    nodes, idx, n = [], start + 1, len(txt)
    while idx < n:
        while idx < n and txt[idx] in " \t\r\n,":
            idx += 1
        if idx >= n or txt[idx] == ']':
            break
        try:
            obj, idx = dec.raw_decode(txt, idx)
        except json.JSONDecodeError:
            break  # reached the truncated last record
        nodes.append(obj)
    print("warning: %s was truncated; salvaged %d complete nodes"
          % (path, len(nodes)), file=sys.stderr)
    return nodes


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("json", nargs="?", default="decision_tree.json")
    ap.add_argument("--no-html", action="store_true")
    ap.add_argument("--dot", action="store_true")
    ap.add_argument("--report", action="store_true",
                    help="write a full step-by-step Markdown report")
    args = ap.parse_args()

    if not os.path.exists(args.json):
        sys.exit("error: %s not found (run ostrich first)" % args.json)
    nodes = load_nodes(args.json)
    if not nodes:
        sys.exit("decision tree is empty")

    render_terminal(nodes)
    if not args.no_html:
        render_html(nodes, args.json, "decision_tree.html")
    if args.dot:
        render_dot(nodes, "decision_tree.dot")
    if args.report:
        render_report(nodes, args.json, "decision_tree.md")


if __name__ == "__main__":
    main()
