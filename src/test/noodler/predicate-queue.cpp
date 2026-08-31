#include <catch2/catch_test_macros.hpp>

#include "smt/theory_str_noodler/solving_state.h"

using namespace smt::noodler;

namespace {

Predicate predicate_with_weight(const std::string& name, size_t weight) {
    std::vector<BasicTerm> left_side(
        weight, BasicTerm{BasicTermType::Variable, name});
    return Predicate::create_equation(left_side, {});
}

void check_and_pop(PredicateQueue& queue, const Predicate& expected, bool priority) {
    REQUIRE_FALSE(queue.empty());
    CHECK(queue.top() == expected);
    CHECK(queue.top_priority() == priority);
    queue.pop();
}

}

TEST_CASE("PredicateQueue ordering", "[noodler][predicate-queue]") {
    SECTION("disabled heuristic preserves FIFO order") {
        PredicateQueue queue{false};
        const Predicate deep_light = predicate_with_weight("deep-light", 1);
        const Predicate high = predicate_with_weight("high", 2);
        const Predicate shallow_heavy = predicate_with_weight("shallow-heavy", 5);

        queue.push(deep_light, false, 8);
        queue.push(high, true, 0);
        queue.push(shallow_heavy, false, 1);

        check_and_pop(queue, deep_light, false);
        check_and_pop(queue, high, true);
        check_and_pop(queue, shallow_heavy, false);
        CHECK(queue.empty());
    }

    SECTION("high-priority predicates are FIFO regardless of weight") {
        PredicateQueue queue;
        const Predicate heavy = predicate_with_weight("heavy", 5);
        const Predicate light = predicate_with_weight("light", 1);
        const Predicate medium = predicate_with_weight("medium", 3);

        queue.push(heavy, true);
        queue.push(light, true);
        queue.push(medium, true);

        check_and_pop(queue, heavy, true);
        check_and_pop(queue, light, true);
        check_and_pop(queue, medium, true);
        CHECK(queue.empty());
    }

    SECTION("low-priority predicates retain weight order") {
        PredicateQueue queue;
        const Predicate heavy = predicate_with_weight("heavy", 5);
        const Predicate first_light = predicate_with_weight("first-light", 1);
        const Predicate medium = predicate_with_weight("medium", 3);
        const Predicate second_light = predicate_with_weight("second-light", 1);

        queue.push(heavy, false);
        queue.push(first_light, false);
        queue.push(medium, false);
        queue.push(second_light, false);

        check_and_pop(queue, first_light, false);
        check_and_pop(queue, second_light, false);
        check_and_pop(queue, medium, false);
        check_and_pop(queue, heavy, false);
        CHECK(queue.empty());
    }

    SECTION("low-priority predicates use depth before weight") {
        PredicateQueue queue;
        const Predicate shallow_heavy = predicate_with_weight("shallow-heavy", 5);
        const Predicate deep_light = predicate_with_weight("deep-light", 1);

        queue.push(deep_light, false, 4);
        queue.push(shallow_heavy, false, 1);

        check_and_pop(queue, shallow_heavy, false);
        check_and_pop(queue, deep_light, false);
    }

    SECTION("weight and insertion order break equal-depth ties") {
        PredicateQueue queue;
        const Predicate heavy = predicate_with_weight("depth-heavy", 4);
        const Predicate first_light = predicate_with_weight("depth-first-light", 1);
        const Predicate second_light = predicate_with_weight("depth-second-light", 1);

        queue.push(heavy, false, 2);
        queue.push(first_light, false, 2);
        queue.push(second_light, false, 2);

        check_and_pop(queue, first_light, false);
        check_and_pop(queue, second_light, false);
        check_and_pop(queue, heavy, false);
    }

    SECTION("high-priority FIFO ignores depth") {
        PredicateQueue queue;
        const Predicate deep = predicate_with_weight("high-deep", 1);
        const Predicate shallow = predicate_with_weight("high-shallow", 1);

        queue.push(deep, true, 8);
        queue.push(shallow, true, 0);

        check_and_pop(queue, deep, true);
        check_and_pop(queue, shallow, true);
    }

    SECTION("a smaller duplicate depth repositions a normal entry") {
        PredicateQueue queue;
        const Predicate updated = predicate_with_weight("updated", 5);
        const Predicate middle = predicate_with_weight("middle", 1);

        queue.push(updated, false, 5);
        queue.push(middle, false, 3);
        queue.push(updated, true, 2);

        REQUIRE(queue.size() == 2);
        CHECK(queue.top_depth() == std::optional<size_t>{2});
        check_and_pop(queue, updated, false);
        check_and_pop(queue, middle, false);
    }

    SECTION("priority bands remain ordered when pushes are interleaved") {
        PredicateQueue queue;
        const Predicate low_heavy = predicate_with_weight("low-heavy", 5);
        const Predicate high_first = predicate_with_weight("high-first", 4);
        const Predicate low_light = predicate_with_weight("low-light", 1);
        const Predicate high_second = predicate_with_weight("high-second", 1);

        queue.push(low_heavy, false);
        queue.push(high_first, true);
        queue.push(low_light, false);
        queue.push(high_second, true);

        check_and_pop(queue, high_first, true);
        check_and_pop(queue, high_second, true);
        check_and_pop(queue, low_light, false);
        check_and_pop(queue, low_heavy, false);
        CHECK(queue.empty());
    }

    SECTION("duplicate pushes preserve the original priority and position") {
        PredicateQueue queue;
        const Predicate original = predicate_with_weight("original", 3);
        const Predicate high = predicate_with_weight("high", 1);

        queue.push(original, false);
        queue.push(original, true);
        queue.push(high, true);

        REQUIRE(queue.size() == 2);
        check_and_pop(queue, high, true);
        check_and_pop(queue, original, false);
        CHECK(queue.empty());
    }

    SECTION("erase preserves order and priority") {
        PredicateQueue queue;
        const Predicate high_first = predicate_with_weight("high-first", 2);
        const Predicate high_second = predicate_with_weight("high-second", 1);
        const Predicate low = predicate_with_weight("low", 3);

        queue.push(high_first, true);
        queue.push(high_second, true);
        queue.push(low, false);

        CHECK(queue.erase(high_second));
        CHECK_FALSE(queue.erase(high_second));
        check_and_pop(queue, high_first, true);
        check_and_pop(queue, low, false);
        CHECK(queue.empty());
    }
}
