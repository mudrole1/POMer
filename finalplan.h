#ifndef FINALPLAN_H
#define FINALPLAN_H

#include "vhpop/chain.h"
#include "vhpop/link.h"
#include <memory>
#include <vector>
#include "steptimed.h"

class FinalPlan
{
private:
    std::unique_ptr<std::vector<std::shared_ptr<Link> > > links_;
    std::unique_ptr<const TemporalOrderings> orderings_;
    //pair of step and "start" or "end" of step
    std::unique_ptr<std::vector<std::pair<std::shared_ptr<StepTimed>, std::pair<std::string, size_t> > > > steps_;

public:

    std::map<std::shared_ptr<StepTimed>, size_t> unfinished_actions;
    std::map<std::string, std::pair<StepTime, int>> achievers;
    std::map<std::string, std::pair<StepTime, int>> deleters;
    FinalPlan();

    void addLink(std::shared_ptr<Link>);
    void changeLink(int, bool);
    const TemporalOrderings * getOrderings()
    {
        return orderings_.get();
    }
    void setOrderings(std::unique_ptr<const TemporalOrderings> ord)
    {
        orderings_ = std::move(ord);
    }

    std::vector<std::shared_ptr<Link> > * getLinks()
    {
        return links_.get();
    }

    void addStep(std::pair<std::shared_ptr<StepTimed>, std::pair<std::string, size_t> >);

    //return step with the id
    std::shared_ptr<StepTimed> getStep(size_t id);


    //TODO probably I will need remove step, remove link etc...
};

#endif // FINALPLAN_H
