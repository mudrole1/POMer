#ifndef STEPTIMED
#define STEPTIMED

#include <memory>
#include <iostream>

#include "task.h"
#include "vhpop/plans.h"


#include "vhpop/parameters.h"




class StepTimed
{
    std::unique_ptr<Step> step;
    Task * task; //normal pointer - this object doesnt own task pointer
    int merged; //1 if it is in usedList, 0 if it is still in activeList, -1 if it is not in any list
    bool backtrack;
    int endTime; //if the time is -1 - it is the start of an action. If the time is set, it is the end of an action

public:
    StepTimed(std::unique_ptr<Step>, Task *);
    StepTimed(std::unique_ptr<Step>, Task *,int);
    StepTimed();
    StepTimed(const StepTimed&);
    Step * getStep();
    Task * getTask();
    void setMerged(int);
    int getMerged();
    void setBacktrack(bool);
    bool getBacktrack();
    int getEndTime();
    void setEndTime(int);
    friend std::ostream& operator<<(std::ostream&, const StepTimed&);
};


#endif // STEPTIMED

