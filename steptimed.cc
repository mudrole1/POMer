#include <memory>
#include <iostream>

#include "task.h"
#include "vhpop/plans.h"
#include "steptimed.h"
#include "vhpop/bindings.h"



StepTimed::StepTimed(std::unique_ptr<Step> s, Task * t)
{
    step = std::move(s);
    task = t;
    merged = -1;
    backtrack = false;
    endTime = -1;
}

StepTimed::StepTimed(std::unique_ptr<Step> s, Task * t, int m)
{
    step = std::move(s);
    task = t;
    merged = m;
    backtrack = false;
    endTime = -1;
}

StepTimed::StepTimed()
{
    step = std::unique_ptr<Step>();
    task = NULL;
    merged = -1;
    backtrack = false;
    endTime = -1;
}

StepTimed::StepTimed(const StepTimed & o)
    :merged(o.merged), backtrack(o.backtrack), endTime(o.endTime)
{
    if(o.step != 0)
        this->step = std::unique_ptr<Step>(new Step(*o.step.get()));
    else
        this->step = std::unique_ptr<Step>();

    if(o.task != 0)
        this->task = new Task(*o.task);
    else
        this->task = 0;

}

Step * StepTimed::getStep()
{
    return step.get();
}

Task * StepTimed::getTask()
{
    return task;
}

void StepTimed::setMerged(int m)
{
    merged = m;
}

int StepTimed::getMerged()
{
    return merged;
}

void StepTimed::setBacktrack(bool m)
{
    backtrack= m;
}

bool StepTimed::getBacktrack()
{
    return backtrack;
}

int StepTimed::getEndTime()
{
   return endTime;
}
void StepTimed::setEndTime(int et)
{
    endTime = et;
}

std::ostream& operator<<(std::ostream& os, const StepTimed& s)
{

   const Bindings* bindings = s.task->getPlan()->bindings_anytime();

   os << "[";
   s.step->action().print(os, s.step->id(), *bindings);
   os<< "\n";
   os << "merged " << s.merged;
   os << "]\n";

   return os;
}
