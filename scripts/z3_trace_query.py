#!/usr/bin/env python3
"""Extract a compact description of one solving state from Noodler's YAML trace."""

import argparse
import sys
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Set, Tuple


EXIT_NOT_FOUND = 1
EXIT_USAGE = 2
EXIT_TRACE_ERROR = 3

SNAPSHOT_FIELD_ORDER = (
    "inclusions",
    "transducers",
    "predicates-to-process",
    "length-vars",
    "noodle-division",
)
RELATIONSHIP_FIELD_ORDER = ("ancestors", "children", "siblings")
FIELD_ORDER = SNAPSHOT_FIELD_ORDER + RELATIONSHIP_FIELD_ORDER
KNOWN_STATUSES = {"pending", "exploring", "explored", "sat", "unsat"}
DEFAULT_MAX_COUNT = 20


class TraceError(Exception):
    """The trace cannot be queried safely."""


class SExpressionError(ValueError):
    """An SMT-LIB S-expression is not balanced or otherwise well formed."""


@dataclass
class NoodleLeft:
    var: str
    new_vars: List[str]


@dataclass
class NoodleRight:
    div_vars: List[str]
    new_vars: List[str]


@dataclass
class NoodleDivision:
    left: List[NoodleLeft]
    right: List[NoodleRight]


@dataclass
class SearchNode:
    node_id: str
    predecessor: Optional[str]
    inclusions: List[str]
    inclusions_on_cycle: List[bool]
    inclusion_sides: List[Tuple[str, str]]
    transducers: List[str]
    predicates_to_process: List[str]
    substitution_map: Dict[str, List[str]]
    aut_assignment: Dict[str, str]
    length_vars: List[str]
    noodle_division: Optional[NoodleDivision]
    status: str


@dataclass
class QueryContext:
    target: Optional[SearchNode]
    tree_nodes: List[SearchNode]
    total_states: int


class StoreMaxCountOverride(argparse.Action):
    """Store one --max-count:FIELD value and reject duplicate overrides."""

    def __call__(self, parser, namespace, values, option_string=None) -> None:
        overrides = dict(getattr(namespace, self.dest, None) or {})
        field = option_string.split(":", 1)[1]
        if field in overrides:
            parser.error("{} may not be repeated".format(option_string))
        overrides[field] = values
        setattr(namespace, self.dest, overrides)


def parse_state_number(value: str) -> int:
    if not value or not value.isascii() or not value.isdigit():
        raise argparse.ArgumentTypeError("STATE_NUMBER must be a non-negative decimal integer")
    return int(value)


def parse_max_count(value: str) -> int:
    if not value or not value.isascii() or not value.isdigit():
        raise argparse.ArgumentTypeError("COUNT must be a non-negative decimal integer")
    return int(value)


def unique_in_order(values: Sequence[str]) -> List[str]:
    seen: Set[str] = set()
    result: List[str] = []
    for value in values:
        if value not in seen:
            seen.add(value)
            result.append(value)
    return result


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Describe one SolvingState from Noodler's .z3-trace YAML stream.",
        epilog=(
            "When no field options are passed, all fields are printed by default, "
            "unless --variable is used; --variable alone prints only the requested "
            "variable representations."
        ),
    )
    parser.add_argument(
        "--trace",
        default=".z3-trace",
        help="path to the YAML trace (default: .z3-trace)",
    )
    parser.add_argument("state_number", metavar="STATE_NUMBER", type=parse_state_number)
    for field in FIELD_ORDER:
        parser.add_argument(
            "--" + field,
            action="store_true",
            help="print the {} field".format(field),
        )
    parser.add_argument(
        "--variable",
        action="append",
        default=[],
        help="variable whose automaton or substitution should be printed; repeatable",
    )
    parser.add_argument(
        "--max-count",
        type=parse_max_count,
        default=DEFAULT_MAX_COUNT,
        metavar="COUNT",
        help="uniform per-field output limit (default: {})".format(DEFAULT_MAX_COUNT),
    )
    parser.add_argument(
        *("--max-count:" + field for field in FIELD_ORDER),
        action=StoreMaxCountOverride,
        dest="max_count_overrides",
        type=parse_max_count,
        default=None,
        metavar="COUNT",
        help="override the output limit for one field",
    )
    return parser.parse_args(argv)


def _skip_whitespace(text: str, index: int) -> int:
    while index < len(text) and text[index].isspace():
        index += 1
    return index


def _scan_string(text: str, index: int) -> int:
    """Return the index after an SMT-LIB string beginning at index."""
    index += 1
    while index < len(text):
        if text[index] != '"':
            index += 1
            continue
        if index + 1 < len(text) and text[index + 1] == '"':
            index += 2
            continue
        return index + 1
    raise SExpressionError("unterminated SMT-LIB string")


def _scan_quoted_symbol(text: str, index: int) -> int:
    """Return the index after a quoted SMT-LIB symbol beginning at index."""
    index += 1
    while index < len(text):
        if text[index] == "\\" and index + 1 < len(text):
            index += 2
        elif text[index] == "|":
            return index + 1
        else:
            index += 1
    raise SExpressionError("unterminated quoted SMT-LIB symbol")


def _scan_parenthesized(text: str, index: int) -> int:
    depth = 0
    while index < len(text):
        char = text[index]
        if char == '"':
            index = _scan_string(text, index)
        elif char == "|":
            index = _scan_quoted_symbol(text, index)
        elif char == "(":
            depth += 1
            index += 1
        elif char == ")":
            depth -= 1
            index += 1
            if depth == 0:
                return index
            if depth < 0:
                raise SExpressionError("unexpected closing parenthesis")
        else:
            index += 1
    raise SExpressionError("unterminated parenthesized SMT-LIB term")


def _scan_term(text: str, index: int) -> Tuple[str, int]:
    index = _skip_whitespace(text, index)
    if index >= len(text) or text[index] == ")":
        raise SExpressionError("expected SMT-LIB term")

    start = index
    if text[index] == "(":
        index = _scan_parenthesized(text, index)
    elif text[index] == '"':
        index = _scan_string(text, index)
    elif text[index] == "|":
        index = _scan_quoted_symbol(text, index)
    else:
        while index < len(text) and not text[index].isspace() and text[index] not in "()":
            index += 1
        if index == start:
            raise SExpressionError("expected SMT-LIB atom")
    return text[start:index], index


def split_outer_equality(text: str) -> Optional[Tuple[str, str]]:
    """Split a binary top-level (= lhs rhs), returning None for another form."""
    index = _skip_whitespace(text, 0)
    if index >= len(text) or text[index] != "(":
        return None
    index += 1

    try:
        operator, index = _scan_term(text, index)
        if operator != "=":
            return None
        lhs, index = _scan_term(text, index)
        rhs, index = _scan_term(text, index)
        index = _skip_whitespace(text, index)
        if index >= len(text) or text[index] != ")":
            return None
        index = _skip_whitespace(text, index + 1)
        if index != len(text):
            return None
        return lhs, rhs
    except SExpressionError:
        return None


def _require_key(mapping: dict, key: str, context: str):
    if key not in mapping:
        raise TraceError("{} is missing required field {!r}".format(context, key))
    return mapping[key]


def _list_value(value, context: str) -> list:
    if value is None:
        return []
    if not isinstance(value, list):
        raise TraceError("{} must be a list".format(context))
    return value


def _mapping_value(value, context: str) -> dict:
    if value is None:
        return {}
    if not isinstance(value, dict):
        raise TraceError("{} must be a mapping".format(context))
    return value


def _string_list(value, context: str) -> List[str]:
    result = _list_value(value, context)
    for index, item in enumerate(result):
        if not isinstance(item, str):
            raise TraceError("{}[{}] must be a string".format(context, index))
    return list(result)


def _is_node_id(value: str) -> bool:
    prefix = "SolvingState"
    suffix = value[len(prefix):] if value.startswith(prefix) else ""
    return bool(suffix) and suffix.isascii() and suffix.isdigit()


def _parse_noodle_division(value, context: str) -> Optional[NoodleDivision]:
    if value is None:
        return None
    mapping = _mapping_value(value, context)
    left_values = _list_value(_require_key(mapping, "left", context), context + ".left")
    right_values = _list_value(_require_key(mapping, "right", context), context + ".right")

    left: List[NoodleLeft] = []
    for index, entry in enumerate(left_values):
        entry_context = "{}.left[{}]".format(context, index)
        if not isinstance(entry, dict):
            raise TraceError("{} must be a mapping".format(entry_context))
        var = _require_key(entry, "var", entry_context)
        if not isinstance(var, str):
            raise TraceError("{}.var must be a string".format(entry_context))
        new_vars = _string_list(
            _require_key(entry, "new_vars", entry_context), entry_context + ".new_vars"
        )
        left.append(NoodleLeft(var=var, new_vars=new_vars))

    right: List[NoodleRight] = []
    for index, entry in enumerate(right_values):
        entry_context = "{}.right[{}]".format(context, index)
        if not isinstance(entry, dict):
            raise TraceError("{} must be a mapping".format(entry_context))
        div_vars = _string_list(
            _require_key(entry, "div_vars", entry_context), entry_context + ".div_vars"
        )
        new_vars = _string_list(
            _require_key(entry, "new_vars", entry_context), entry_context + ".new_vars"
        )
        right.append(NoodleRight(div_vars=div_vars, new_vars=new_vars))

    return NoodleDivision(left=left, right=right)


def _parse_node(value, document_number: int, node_number: int) -> SearchNode:
    context = "document {} node {}".format(document_number, node_number)
    if not isinstance(value, dict):
        raise TraceError("{} must be a mapping".format(context))

    node_id = _require_key(value, "id", context)
    if not isinstance(node_id, str) or not _is_node_id(node_id):
        raise TraceError("{}.id must have form SolvingState<ID>".format(context))
    context = "document {} node {} ({})".format(document_number, node_number, node_id)

    predecessor = _require_key(value, "pre", context)
    if predecessor is not None:
        if not isinstance(predecessor, str) or (
            predecessor != "init" and not _is_node_id(predecessor)
        ):
            raise TraceError("{}.pre must be init, null, or a SolvingState<ID>".format(context))

    inclusions = _string_list(
        _require_key(value, "inclusions", context), context + ".inclusions"
    )
    raw_cycle_flags = _list_value(
        _require_key(value, "inclusions_on_cycle", context),
        context + ".inclusions_on_cycle",
    )
    if len(raw_cycle_flags) != len(inclusions):
        raise TraceError(
            "{}.inclusions_on_cycle must have the same length as inclusions".format(context)
        )
    if any(type(flag) is not bool for flag in raw_cycle_flags):
        raise TraceError("{}.inclusions_on_cycle must contain only Booleans".format(context))
    inclusions_on_cycle = list(raw_cycle_flags)

    inclusion_sides: List[Tuple[str, str]] = []
    for index, inclusion in enumerate(inclusions):
        sides = split_outer_equality(inclusion)
        if sides is None:
            raise TraceError("{}.inclusions[{}] must be a binary equality".format(context, index))
        inclusion_sides.append(sides)

    transducers = _string_list(
        _require_key(value, "transducers", context), context + ".transducers"
    )
    predicates_to_process = _string_list(
        _require_key(value, "predicates_to_process", context),
        context + ".predicates_to_process",
    )
    length_vars = _string_list(
        _require_key(value, "length_vars", context), context + ".length_vars"
    )

    raw_substitution_map = _mapping_value(
        _require_key(value, "substitution_map", context), context + ".substitution_map"
    )
    substitution_map: Dict[str, List[str]] = {}
    for var, replacement in raw_substitution_map.items():
        if not isinstance(var, str):
            raise TraceError("{}.substitution_map keys must be strings".format(context))
        substitution_map[var] = _string_list(
            replacement, "{}.substitution_map[{!r}]".format(context, var)
        )

    raw_aut_assignment = _mapping_value(
        _require_key(value, "aut_assignment", context), context + ".aut_assignment"
    )
    aut_assignment: Dict[str, str] = {}
    for var, dot in raw_aut_assignment.items():
        if not isinstance(var, str) or not isinstance(dot, str):
            raise TraceError("{}.aut_assignment must map strings to DOT strings".format(context))
        aut_assignment[var] = dot

    overlap = set(substitution_map).intersection(aut_assignment)
    if overlap:
        raise TraceError(
            "{} represents variable {!r} in both maps".format(context, sorted(overlap)[0])
        )

    status = value.get("status", "pending")
    if not isinstance(status, str) or status not in KNOWN_STATUSES:
        raise TraceError("{}.status is not recognized".format(context))
    if status == "sat" and predicates_to_process:
        raise TraceError("{} has status sat but a non-empty predicate queue".format(context))
    if status == "explored" and not predicates_to_process:
        raise TraceError("{} has status {} but an empty predicate queue".format(context, status))

    noodle_division = _parse_noodle_division(
        value.get("noodle_division"), context + ".noodle_division"
    )

    return SearchNode(
        node_id=node_id,
        predecessor=predecessor,
        inclusions=inclusions,
        inclusions_on_cycle=inclusions_on_cycle,
        inclusion_sides=inclusion_sides,
        transducers=transducers,
        predicates_to_process=predicates_to_process,
        substitution_map=substitution_map,
        aut_assignment=aut_assignment,
        length_vars=length_vars,
        noodle_division=noodle_division,
        status=status,
    )


def _validate_predecessors(nodes: Sequence[SearchNode], document_number: int) -> None:
    by_id = {node.node_id: node for node in nodes}
    for node in nodes:
        predecessor = node.predecessor
        if predecessor not in (None, "init") and predecessor not in by_id:
            raise TraceError(
                "document {} node {} names predecessor {} outside its search tree".format(
                    document_number, node.node_id, predecessor
                )
            )

    colors: Dict[str, int] = {}
    for start in by_id:
        if colors.get(start) == 2:
            continue
        path: List[str] = []
        current = start
        while current in by_id and colors.get(current, 0) == 0:
            colors[current] = 1
            path.append(current)
            predecessor = by_id[current].predecessor
            if predecessor in (None, "init"):
                current = ""
            else:
                current = predecessor
        if current in by_id and colors.get(current) == 1:
            raise TraceError(
                "document {} contains a predecessor cycle involving {}".format(
                    document_number, current
                )
            )
        for node_id in path:
            colors[node_id] = 2


def _yaml_error_message(error) -> str:
    mark = getattr(error, "problem_mark", None)
    problem = getattr(error, "problem", None) or "invalid YAML"
    if mark is None:
        return "invalid YAML: {}".format(problem)
    return "invalid YAML at line {}, column {}: {}".format(
        mark.line + 1, mark.column + 1, problem
    )


def _load_yaml_documents(stream, yaml_module):
    """Use LibYAML's safe loader when available, with a portable safe fallback."""
    c_safe_loader = getattr(yaml_module, "CSafeLoader", None)
    if c_safe_loader is not None:
        return yaml_module.load_all(stream, Loader=c_safe_loader)
    return yaml_module.safe_load_all(stream)


def load_query_context(trace_path: str, target_id: str, yaml_module) -> QueryContext:
    seen_ids: Set[str] = set()
    target: Optional[SearchNode] = None
    target_tree_nodes: List[SearchNode] = []
    document_count = 0

    try:
        with open(trace_path, "r", encoding="utf-8") as stream:
            try:
                for document_count, document in enumerate(
                    _load_yaml_documents(stream, yaml_module), start=1
                ):
                    if not isinstance(document, dict):
                        raise TraceError("document {} must be a mapping".format(document_count))
                    document_type = document.get("type")
                    if not isinstance(document_type, str):
                        raise TraceError(
                            "document {} must have a string type".format(document_count)
                        )
                    if document_type != "search_tree":
                        continue

                    raw_nodes = _list_value(
                        _require_key(document, "nodes", "document {}".format(document_count)),
                        "document {}.nodes".format(document_count),
                    )
                    num_explored = _require_key(
                        document, "num_explored", "document {}".format(document_count)
                    )
                    if (
                        not isinstance(num_explored, int)
                        or isinstance(num_explored, bool)
                        or num_explored < 0
                    ):
                        raise TraceError(
                            "document {}.num_explored must be a non-negative integer".format(
                                document_count
                            )
                        )

                    nodes: List[SearchNode] = []
                    for node_number, raw_node in enumerate(raw_nodes):
                        node = _parse_node(raw_node, document_count, node_number)
                        if node.node_id in seen_ids:
                            raise TraceError("duplicate node ID {}".format(node.node_id))
                        seen_ids.add(node.node_id)
                        nodes.append(node)
                    _validate_predecessors(nodes, document_count)
                    for node in nodes:
                        if node.node_id == target_id:
                            target = node
                            target_tree_nodes = nodes
                            break
            except yaml_module.YAMLError as error:
                raise TraceError(_yaml_error_message(error)) from error
    except (OSError, UnicodeError) as error:
        raise TraceError("cannot read {!r}: {}".format(trace_path, error)) from error

    if document_count == 0:
        raise TraceError("trace {!r} is empty".format(trace_path))
    return QueryContext(
        target=target,
        tree_nodes=target_tree_nodes,
        total_states=len(seen_ids),
    )


def selected_fields(
    requested_fields: Sequence[str], variables: Sequence[str]
) -> Set[str]:
    if requested_fields:
        return set(requested_fields)
    if variables:
        return set()
    return set(FIELD_ORDER)


def _append_text_block(lines: List[str], text: str, indentation: str = "      ") -> None:
    physical_lines = text.splitlines()
    if not physical_lines:
        physical_lines = [""]
    lines.extend(indentation + line for line in physical_lines)


def _status_description(node: SearchNode) -> str:
    if node.status == "pending":
        if node.predicates_to_process:
            return "not yet popped; the first queued predicate would be processed next"
        return "not yet popped; the candidate has not yet been examined"
    if node.status == "exploring":
        return "the state was popped; processing or a premature length check may be in progress"
    if node.status == "explored":
        return "the first queued predicate was processed from this snapshot"
    if node.status == "unsat":
        if not node.predicates_to_process:
            return "a mandatory length check pruned the candidate before it was returned"
        return "a premature length check pruned the state before the first queued predicate was processed"
    return "the predicate queue is empty; this is a candidate for the later length check"


def _format_list(values: Sequence[str]) -> str:
    return "[{}]".format(", ".join(values))


def _field_heading(
    label: str, total: int, shown: int, order: Optional[str] = None
) -> str:
    details = str(total)
    if shown < total:
        details += ", showing {}".format(shown)
    if order is not None:
        details += ", " + order
    return "{} ({}):".format(label, details)


def _append_omission(
    lines: List[str], total: int, shown: int, indentation: str = "  "
) -> None:
    if shown < total:
        lines.append("{}... {} omitted".format(indentation, total - shown))


def _render_header(lines: List[str], node: SearchNode, total_states: int) -> None:
    predecessor = "none" if node.predecessor is None else node.predecessor
    lines.append("State: {}".format(node.node_id))
    lines.append("Predecessor: {}".format(predecessor))
    lines.append("Status: {} ({})".format(node.status, _status_description(node)))
    lines.append("Total states: {}".format(total_states))


def _render_inclusions(lines: List[str], node: SearchNode, max_count: int) -> None:
    if not node.inclusions:
        lines.append("Inclusions (0): none")
        return
    shown = min(len(node.inclusions), max_count)
    lines.append(_field_heading("Inclusions", len(node.inclusions), shown))
    for index, (inclusion, on_cycle) in enumerate(
        zip(node.inclusions[:shown], node.inclusions_on_cycle[:shown])
    ):
        lines.append("  [{}] {}".format(index, "on cycle" if on_cycle else "not on cycle"))
        _append_text_block(lines, inclusion)
    _append_omission(lines, len(node.inclusions), shown)


def _render_transducers(lines: List[str], node: SearchNode, max_count: int) -> None:
    if not node.transducers:
        lines.append("Transducers (0): none")
        return
    shown = min(len(node.transducers), max_count)
    lines.append(_field_heading("Transducers", len(node.transducers), shown))
    for index, transducer in enumerate(node.transducers[:shown]):
        lines.append("  [{}]".format(index))
        _append_text_block(lines, transducer)
    _append_omission(lines, len(node.transducers), shown)


def _classify_predicate(node: SearchNode, predicate: str) -> Tuple[str, Optional[bool]]:
    sides = split_outer_equality(predicate)
    if sides is not None:
        matching_flags = [
            flag
            for inclusion_sides, flag in zip(
                node.inclusion_sides, node.inclusions_on_cycle
            )
            if sides == inclusion_sides or sides == tuple(reversed(inclusion_sides))
        ]
        if matching_flags:
            return "inclusion", any(matching_flags)
    if predicate in node.transducers:
        return "transducer", None
    return "predicate", None


def _first_predicate_action(status: str) -> str:
    if status == "pending":
        return "next if the state is popped"
    if status == "exploring":
        return "selected; processing or a length check may be in progress"
    if status == "explored":
        return "processed from this snapshot"
    if status == "unsat":
        return "not processed; state pruned by a premature length check"
    return "queued"


def _render_predicates(lines: List[str], node: SearchNode, max_count: int) -> None:
    predicates = node.predicates_to_process
    if not predicates:
        lines.append("Predicates to process (0): none")
        return
    shown = min(len(predicates), max_count)
    lines.append(
        _field_heading("Predicates to process", len(predicates), shown, "best first")
    )
    for index, predicate in enumerate(predicates[:shown]):
        predicate_type, on_cycle = _classify_predicate(node, predicate)
        attributes = [predicate_type]
        if predicate_type == "inclusion":
            attributes.append("on cycle" if on_cycle else "not on cycle")
        elif predicate_type == "predicate":
            attributes.append("cycle unknown")
        attributes.append(_first_predicate_action(node.status) if index == 0 else "queued")
        lines.append("  [{}] {}".format(index, "; ".join(attributes)))
        _append_text_block(lines, predicate)
    _append_omission(lines, len(predicates), shown)


def _render_length_vars(lines: List[str], node: SearchNode, max_count: int) -> None:
    if not node.length_vars:
        lines.append("Length variables (0): none")
        return
    shown = min(len(node.length_vars), max_count)
    lines.append(_field_heading("Length variables", len(node.length_vars), shown))
    lines.extend("  - " + var for var in node.length_vars[:shown])
    _append_omission(lines, len(node.length_vars), shown)


def _render_noodle_division(lines: List[str], node: SearchNode, max_count: int) -> None:
    division = node.noodle_division
    if division is None:
        lines.append("Noodle division: none recorded")
        return
    lines.append("Noodle division:")
    if division.left:
        shown = min(len(division.left), max_count)
        if shown < len(division.left):
            lines.append("  " + _field_heading("Left", len(division.left), shown))
        else:
            lines.append("  Left:")
        for index, entry in enumerate(division.left[:shown]):
            lines.append(
                "    [{}] variable {} -> segments {}".format(
                    index, entry.var, _format_list(entry.new_vars)
                )
            )
        _append_omission(lines, len(division.left), shown, indentation="    ")
    else:
        lines.append("  Left: none")
    if division.right:
        shown = min(len(division.right), max_count)
        if shown < len(division.right):
            lines.append("  " + _field_heading("Right", len(division.right), shown))
        else:
            lines.append("  Right:")
        for index, entry in enumerate(division.right[:shown]):
            lines.append(
                "    [{}] division {} -> segments {}".format(
                    index, _format_list(entry.div_vars), _format_list(entry.new_vars)
                )
            )
        _append_omission(lines, len(division.right), shown, indentation="    ")
    else:
        lines.append("  Right: none")


def _render_related_nodes(
    lines: List[str], label: str, related: Sequence[SearchNode], max_count: int, order: str
) -> None:
    if not related:
        lines.append("{} (0): none".format(label))
        return
    shown = min(len(related), max_count)
    lines.append(_field_heading(label, len(related), shown, order))
    for index, related_node in enumerate(related[:shown]):
        lines.append(
            "  [{}] {} [{}]".format(index, related_node.node_id, related_node.status)
        )
    _append_omission(lines, len(related), shown)


def _render_ancestors(
    lines: List[str], node: SearchNode, tree_nodes: Sequence[SearchNode], max_count: int
) -> None:
    by_id = {tree_node.node_id: tree_node for tree_node in tree_nodes}
    ancestors: List[SearchNode] = []
    predecessor = node.predecessor
    while predecessor not in (None, "init"):
        ancestor = by_id[predecessor]
        ancestors.append(ancestor)
        predecessor = ancestor.predecessor
    _render_related_nodes(lines, "Ancestors", ancestors, max_count, "nearest first")


def _render_children(
    lines: List[str], node: SearchNode, tree_nodes: Sequence[SearchNode], max_count: int
) -> None:
    children = [
        tree_node for tree_node in tree_nodes if tree_node.predecessor == node.node_id
    ]
    _render_related_nodes(lines, "Children", children, max_count, "trace order")


def _render_siblings(
    lines: List[str], node: SearchNode, tree_nodes: Sequence[SearchNode], max_count: int
) -> None:
    if node.predecessor in (None, "init"):
        siblings: List[SearchNode] = []
    else:
        siblings = [
            tree_node
            for tree_node in tree_nodes
            if tree_node.predecessor == node.predecessor
            and tree_node.node_id != node.node_id
        ]
    _render_related_nodes(lines, "Siblings", siblings, max_count, "trace order")


def _render_variables(
    lines: List[str], node: SearchNode, variables: Sequence[str]
) -> List[str]:
    found_lines: List[str] = []
    missing: List[str] = []
    for var in variables:
        if var in node.aut_assignment:
            found_lines.append("  {}: automaton".format(var))
            _append_text_block(found_lines, node.aut_assignment[var], indentation="    ")
        elif var in node.substitution_map:
            found_lines.append(
                "  {}: substitution {}".format(var, _format_list(node.substitution_map[var]))
            )
        else:
            missing.append(var)

    if found_lines:
        lines.append("Variables:")
        lines.extend(found_lines)
    else:
        lines.append("Variables: none found")
    return missing


def render_node(
    node: SearchNode,
    tree_nodes: Sequence[SearchNode],
    total_states: int,
    fields: Set[str],
    variables: Sequence[str],
    max_counts: Dict[str, int],
) -> Tuple[str, List[str]]:
    lines: List[str] = []
    _render_header(lines, node, total_states)

    renderers = {
        "inclusions": _render_inclusions,
        "transducers": _render_transducers,
        "predicates-to-process": _render_predicates,
        "length-vars": _render_length_vars,
        "noodle-division": _render_noodle_division,
    }
    for field in FIELD_ORDER:
        if field in fields:
            lines.append("")
            if field == "ancestors":
                _render_ancestors(lines, node, tree_nodes, max_counts[field])
            elif field == "children":
                _render_children(lines, node, tree_nodes, max_counts[field])
            elif field == "siblings":
                _render_siblings(lines, node, tree_nodes, max_counts[field])
            else:
                renderers[field](lines, node, max_counts[field])

    missing: List[str] = []
    if variables:
        lines.append("")
        missing = _render_variables(lines, node, variables)
    return "\n".join(lines) + "\n", missing


def main(argv: Sequence[str]) -> int:
    args = parse_args(argv)
    requested_fields = [
        field for field in FIELD_ORDER if getattr(args, field.replace("-", "_"))
    ]
    fields = selected_fields(requested_fields, args.variable)
    variables = unique_in_order(args.variable)
    overrides = args.max_count_overrides or {}
    max_counts = {field: overrides.get(field, args.max_count) for field in FIELD_ORDER}
    target_id = "SolvingState{}".format(args.state_number)

    try:
        import yaml
    except ImportError:
        print("error: PyYAML is required; install it with 'python3 -m pip install PyYAML'", file=sys.stderr)
        return EXIT_TRACE_ERROR

    try:
        context = load_query_context(args.trace, target_id, yaml)
    except TraceError as error:
        print("error: {}".format(error), file=sys.stderr)
        return EXIT_TRACE_ERROR

    if context.target is None:
        print("error: {} was not found in {!r}".format(target_id, args.trace), file=sys.stderr)
        return EXIT_NOT_FOUND

    node = context.target
    output, missing = render_node(
        node,
        context.tree_nodes,
        context.total_states,
        fields,
        variables,
        max_counts,
    )
    sys.stdout.write(output)
    for var in missing:
        print(
            "error: variable {!r} has no automaton or substitution in {}".format(
                var, node.node_id
            ),
            file=sys.stderr,
        )
    return EXIT_NOT_FOUND if missing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
