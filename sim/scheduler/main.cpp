#include "Scheduler.cpp"

#include <string>
#include <iostream>

int main() {
    Scheduler<5> scb;

    for (int i = 0; i < 5; ++i) {
        scb.initializeUnit(i, 0, 7);
    }

    scb.dispatch(0, 1);
    std::cout << "\n\n";

    for (int i = 0; i < 20; ++i) {
        std::cout << "============ CYCLE " + std::to_string(i) + " ===========\n";

        scb.advance();

        if (!(scb.checkHazard() | scb.checkLatency())) {
            if (scb.issue()) {
                /* Dispatch another instruction only if the
                 * previous was issued */
                int unit = random() % 5;
                int destination = random() % 32;
                scb.dispatch(unit, destination);
            } 
        }

        std::cout << "\n";
        scb.printScoreboard();
        std::cout << "\n\n\n";
    }
}