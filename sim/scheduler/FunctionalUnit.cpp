#ifndef FUNCTIONAL_UNIT_CPP
#define FUNCTIONAL_UNIT_CPP

#include <string>
#include <iostream>

class FunctionalUnit {

private:

    int latency;
    std::string unitName;

    bool executing;

    int destination;
    int remainingCycles;


public: 

    FunctionalUnit() {}

    FunctionalUnit(int name, int unitLatency) {
        std::cout << "[" + std::to_string(name) + "]" + " Created new functional unit! Latency: " + std::to_string(unitLatency) + "\n";

        executing = false;
        destination = 0;
        latency = unitLatency;
        unitName = "Unit " + std::to_string(name);
        remainingCycles = 0;
    }

    /* Start executing */
    void start(int regDest) {
        std::cout << "[" + unitName + "]" + " Started executing instruction!\n";

        remainingCycles = latency;
        destination = regDest;

        executing = true;
    }


    /* Go to next cycle and decrement the remaining cycles */
    void advance() {
        --remainingCycles;

        if (remainingCycles <= 0) {
            std::cout << "[" + unitName + "]" + " Finished executing instruction!\n";
            remainingCycles = 0;
            destination = 0;
            executing = false;
        }
    }


    /* Is currently executing an instruction */
    bool isExecuting() {
        return executing;
    }

    
    int getDestination() {
        return destination;
    }


    int getLatency() {
        return latency;
    }


    int getRemainingCycles() {
        return remainingCycles;
    }

    std::string getName() {
        return unitName;
    }
};

#endif 