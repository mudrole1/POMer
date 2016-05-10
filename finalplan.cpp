#include "finalplan.h"

FinalPlan::FinalPlan()
{
  links_.reset(new std::vector<std::shared_ptr<Link> >());
  orderings_.reset(new TemporalOrderings());
  steps_.reset(new std::vector<std::pair<std::shared_ptr<StepTimed>, std::pair<std::string, size_t> > >());
}

void FinalPlan::addLink(std::shared_ptr<Link> link)
{
  links_->push_back(link);
}

void FinalPlan::changeLink(int id, bool threat)
{
    links_->at(id)->setThreaten(threat);
}

void FinalPlan::addStep(std::pair<std::shared_ptr<StepTimed>, std::pair<std::string, size_t> > stepT)
{
    steps_->push_back(stepT);
}

//the id is in the sense of "new or global id" in contract to ids saved in StepTimed
std::shared_ptr<StepTimed> FinalPlan::getStep(size_t id)
{
    for(unsigned int i=0;i<steps_->size();i++)
    {
        if(steps_->at(i).second.second == id)
        {
            return steps_->at(i).first;
        }
    }

    return NULL;
}
