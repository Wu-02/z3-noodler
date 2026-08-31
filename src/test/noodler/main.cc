#include <catch2/reporters/catch_reporter_event_listener.hpp>
#include <catch2/reporters/catch_reporter_registrars.hpp>

#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "util/trace.h"

class testRunListener : public Catch::EventListenerBase {
public:
    using Catch::EventListenerBase::EventListenerBase;

    void testRunStarting(const Catch::TestRunInfo &testRunInfo) override {
        memory::initialize(0);
        enable_trace("test_noodler");
    }
};

CATCH_REGISTER_LISTENER(testRunListener)
