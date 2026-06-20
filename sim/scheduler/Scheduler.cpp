#ifndef SCHEDULER_CPP
#define SCHEDULER_CPP

#include <string>
#include <random>
#include <iostream>

#include "FunctionalUnit.cpp"

template <std::size_t N> class Scheduler {

private: 

    FunctionalUnit units[N];

    /* New computation to schedule */
    int newUnit;
    int newDestination;

    int cycles;

public: 

    Scheduler() { }


    bool initializeUnit(int unit, int minLatency, int maxLatency) {
        if (unit >= N) {
            return false;
        }

        int randomLatency = random() % (maxLatency - minLatency + 1) + minLatency;
        units[unit] = FunctionalUnit(unit, randomLatency);

        return true;
    }

    void dispatch(int unit, int destination) {
        std::cout << + "[Unit " + std::to_string(unit) + "] Dispatched new instruction with destination: " + std::to_string(destination) + "\n";

        newUnit = unit;
        newDestination = destination;
    }


    /* Check if there's a RAW hazard */
    bool checkHazard() {
        for (int i = 0; i < N; ++i) {
            if ((units[i].getDestination() == newDestination) & units[i].isExecuting()) {
                std::cout << "RAW hazard detected with the Unit " + std::to_string(i) + "\n";
                return true;
            }
        }

        return false;
    }
    

    /* Check if a functional unit remaining clock
     * cycles overlap the current */
    bool checkLatency() {
        /* Get the overall latency for that unit */
        int latency = units[newUnit].getLatency();

        for (int i = 0; i < N; ++i) {
            /* Increment the latency since the instruction get issued in the next clock cycle */
            if ((units[i].getRemainingCycles() == (latency + 1)) & units[i].isExecuting()) {
                std::cout << "Latency contention with the Unit " + std::to_string(i) + "\n";
                return true;
            }
        }

        return false;
    }


    bool issue() {
        if (!units[newUnit].isExecuting()) {
            std::cout << "[Unit " + std::to_string(newUnit) + "] Issued a new instruction\n";
            units[newUnit].start(newDestination);

            return true;
        } else {
            std::cout << "[Unit " + std::to_string(newUnit) + "] Currently executing!\n";
            return false;
        }

    }


    void advance() {
        for (int i = 0; i < N; ++i) {
            if (units[i].isExecuting()) {
                units[i].advance();
            }
        }

        ++cycles;
    }


    void printScoreboard() {
        std::cout << "\t";

        for (int i = 0; i < N; ++i) {
            std::cout << units[i].getName() + "\t";
        }

        std::cout << "\nREGD    "; 

        for (int i = 0; i < N; ++i) {
            std::cout << std::to_string(units[i].getDestination()) + "\t";
        }

        std::cout << "\nLAT     "; 

        for (int i = 0; i < N; ++i) {
            std::cout << std::to_string(units[i].getRemainingCycles()) + "\t";
        }

        std::cout << "\n"; 
    }
};

#endif 