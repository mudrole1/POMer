/**
  definition of a task

  @author Lenka Mudrova
  @version 1.0 09/12/2015
*/

#include <string>
#include <iostream>
#include <vector>
#include <memory>

#include "task.h"
#include "vhpop/vhpop_callable.h"
#include "vhpop/plans.h"


/* Name of current file. */
/*std::string current_file;
int warning_level;
int verbosity;*/

/**
  constructor
  @param ID of the task, release time, deadline, domain file, problem file
  @return nan, it is constructor
*/
Task::Task(unsigned int ID, double r, double d, std::string d_file, std::string p_file)
{
  id = ID;
  release_date = r;
  deadline = d;
  domain_file = d_file;
  problem_file = p_file;
  name_problem = "";

  plan_available = false;
  duration = -1;
  used = false;

  v_callable = Vhpop_callable();

}

Task::Task(unsigned int ID, double r, double d, std::string d_file, std::string p_file, std::string name_prob)
{
  id = ID;
  release_date = r;
  deadline = d;
  domain_file = d_file;
  problem_file = p_file;
  name_problem = name_prob;

  plan_available = false;
  duration = -1;
  used = false;

  v_callable = Vhpop_callable();

}

Task::Task(const Task & t)
    :id(t.id),release_date(t.release_date),deadline(t.deadline), domain_file(t.domain_file),
      problem_file(t.problem_file), name_problem(t.name_problem),plan_available(t.plan_available),
      duration(t.duration), used(t.used), start_vector(t.start_vector), v_callable(t.v_callable)
{
    if (t.plan != 0)
    {
        const Plan * p = t.plan.get();
        plan = std::unique_ptr<const Plan>(new Plan(*p));
    }
    else
        plan = 0;

    std::vector<std::pair<std::shared_ptr<const Link> ,bool> > links_vector; //to save links

    for(int i=0;i<t.links_vector.size();i++)
    {
        std::shared_ptr<const Link> ptr(new Link(*t.links_vector.at(i).first.get()));
        std::pair<std::shared_ptr<const Link> ,bool> pair(ptr,false);
        this->links_vector.push_back(pair);
    }
}

/*Task::~Task()
{

    for(int i=0;i<links_vector.size();i++)
    {
        //links_vector.at(i).first.release(); //release ownership of the pointer
    }
    //everything else can be done automatically

}*/

unsigned int Task::getID()
{
    return id;
}

double Task::getReleaseDate()
{
    return release_date;
}

double Task::getDeadline()
{
    return deadline;
}

double Task::getDuration()
{
    return duration;
}


const Plan * Task::getPlan()
{
    if (plan_available)
    {
        return plan.get();
    }
    else
        return NULL;
}

std::string Task::getDomain()
{
    return domain_file;
}

std::string Task::getProblem()
{
    return problem_file;
}

void Task::setUsed(bool u)
{
    used = u;
}

bool Task::getUsed()
{
    return used;
}

void Task::setNameProblem(std::string name)
{
    name_problem = name;
}

std::string Task::getNameProblem()
{
    return name_problem;
}

int Task::callPlanner(int argc, char* argv[])
{

    /* Default planning parameters. */
   /*Parameters params;

    verbosity = 0;

    warning_level = 1;

    Vhpop_callable v_callable = Vhpop_callable(current_file,warning_level,verbosity,params);*/


    bool no_flaw_order = true;
    bool no_search_limit = true;
    /*
     * Get command line options.
     */

    if (v_callable.getOptions(argc,argv, no_flaw_order, no_search_limit) == -1)
         return -1;

    if (v_callable.parseFile(argc,argv) == -1)
         return -1;

    const std::string prob = name_problem;
    const Plan * plan_p= v_callable.solve(false,prob);
    if (plan_p != NULL)
    {
        plan_available = true;
        plan.reset(new Plan(*plan_p));
    }
    else
    {
        plan_available = false;
        plan.reset(NULL);
    }



    //todo I can delete this?
    /*for (const Chain<Step>* sc = plan->steps(); sc != NULL; sc = sc->tail)
    {
      const Step step = Step(sc->head);
      if ((step.id() != 0) && (step.id() != Plan::GOAL_ID)) // we dont want fake start and end steps
      {
          steps.push_back(step);
          action.push_back(&step.action());
      }
    }*/



    return 0;
}

std::ostream& operator<<(std::ostream& os, const Task& t)
{
   os << "[" << t.id <<"," << t.release_date << "," <<t.deadline << "," << t.domain_file << "," << t.problem_file << t.name_problem << "]\n";
   return os;
}




