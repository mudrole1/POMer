#include "merging.h"
#include "vhpop/vhpop_callable.h"
#include "vhpop/plans.h"
#include "vhpop/domains.h"
#include "vhpop/problems.h"
#include "vhpop/formulas.h"
#include "task.h"
#include "steptimed.h"
#include "vhpop/bindings.h"
#include "finalplan.h"


#include <iostream>
#include <memory>
#include <stdlib.h>
#include <vector>
#include <sstream>
#include <iostream>
#include <fstream>
#include <limits>
#include <string>
#include <exception>
#include <algorithm>

#include "stdio.h"
#include "string.h"

#include "sys/times.h"
#include "sys/vtimes.h"

#include <ctime>
#include <ratio>
#include <chrono>


static clock_t lastCPU, lastSysCPU, lastUserCPU;
static int numProcessors;


int parseLine(char* line){
         int i = strlen(line);
         while (*line < '0' || *line > '9') line++;
         line[i-3] = '\0';
         i = atoi(line);
         return i;
}


int getVirtualMemory(){ //Note: this value is in KB!
         FILE* file = fopen("/proc/self/status", "r");
         int result = -1;
         char line[128];


         while (fgets(line, 128, file) != NULL){
             if (strncmp(line, "VmSize:", 7) == 0){
                 result = parseLine(line);
                 break;
             }
         }
         fclose(file);
         return result;
}

int getPhysicalMemory(){ //Note: this value is in KB!
    FILE* file = fopen("/proc/self/status", "r");
    int result = -1;
    char line[128];


    while (fgets(line, 128, file) != NULL){
        if (strncmp(line, "VmRSS:", 6) == 0){
            result = parseLine(line);
            break;
        }
    }
    fclose(file);
    return result;
}

/*to get cpu time*/
void init(){
        FILE* file;
        struct tms timeSample;
        char line[128];


        lastCPU = times(&timeSample);
        lastSysCPU = timeSample.tms_stime;
        lastUserCPU = timeSample.tms_utime;


        file = fopen("/proc/cpuinfo", "r");
        numProcessors = 0;
        while(fgets(line, 128, file) != NULL){
            if (strncmp(line, "processor", 9) == 0) numProcessors++;
        }
        fclose(file);
}

double getCurrentValueCPU(){
        struct tms timeSample;
        clock_t now;
        double percent;


        now = times(&timeSample);
        if (now <= lastCPU || timeSample.tms_stime < lastSysCPU ||
            timeSample.tms_utime < lastUserCPU){
            //Overflow detection. Just skip this value.
            percent = -1.0;
        }
        else{
            percent = (timeSample.tms_stime - lastSysCPU) +
                (timeSample.tms_utime - lastUserCPU);
            percent /= (now - lastCPU);
            percent /= numProcessors;
            percent *= 100;
        }
        lastCPU = now;
        lastSysCPU = timeSample.tms_stime;
        lastUserCPU = timeSample.tms_utime;


        return percent;
}

/*class myexception: public exception
{
  virtual const char* what() const throw()
  {
    return "My exception happened";
  }
} myex;*/


//key is domain, value is a vector of valid predicates
std::map<std::string, std::vector<std::string> > current_state;

int g_argc;
char ** g_argv;
int g_temp_prob = 0;

/* Name of current file. */
//std::string current_file;
/* Level of warnings. */
//int warning_level = 1;
/* Verbosity level. */
//int verbosity =1;

/* Default planning parameters. */
//Parameters params;

int g_id = 0; //to rename steps ID in the finalplan

std::shared_ptr<std::vector< std::shared_ptr<Task> > > tasks(new std::vector< std::shared_ptr<Task> >() );
std::shared_ptr< std::vector< std::shared_ptr<Task> > > temp_tasks(new std::vector<std::shared_ptr<Task>>());


//constraints
std::vector< std::vector<int> > constraints;
/*adding all steps from a task to the activeList*/

bool compareSF(std::pair<std::pair<size_t, float>,bool> a, std::pair<std::pair<size_t, float>, bool> b)
{
  return a.first.second < b.first.second;
}

bool findUsed(std::pair<std::pair<size_t, float>,bool> a)
{
    return !a.second;
}

bool zerosPrec(int v)
{
    return (v == 0);
}


bool compareLinks(std::shared_ptr<const Link> a,std::shared_ptr<const Link> b)
{
  const Plan * plan;

  std::string conditionA;
  std::string conditionB;
  if(a->getTaskId()!=-1)
  {
      std::stringstream ss;
      std::ostream &os(ss);
      plan = tasks->at(a->getTaskId())->getPlan();
      a->condition().print(os, a->condition().id(), *plan->bindings_anytime());
      conditionA = ss.str();
  }
  else
  {
      std::cout << "wrong task id\n";
      throw;
  }

  if(b->getTaskId()!=-1)
  {
      std::stringstream ss;
      std::ostream &os(ss);
      plan = tasks->at(b->getTaskId())->getPlan();
      b->condition().print(os, b->condition().id(), *plan->bindings_anytime());
      conditionB = ss.str();
  }
  else
  {
      std::cout << "wrong task id\n";
      throw;
  }


  if((a->from_id() == b->from_id())&&(a->to_id() == b->to_id())
          &&(a->getTaskId() == b->getTaskId())&&(conditionA == conditionB))
  {
      return true;
  }
  else
      return false;
}
//is this id already in active_list?
bool compareSteps(std::shared_ptr<std::vector< std::shared_ptr<StepTimed> > > active_list, Step step)
{
    bool ret = false;
    for(int i=0;i<active_list->size();i++)
    {
        Step acStep = *active_list->at(i)->getStep();
        if(acStep == step)
        {
            ret =true;
            break;
        }
    }
    return ret;
}

bool compareDeadlines(const std::pair<double, int>& firstElem, const std::pair<double, int>& secondElem) {
  return firstElem.first < secondElem.first;

}

bool taskUnused(std::shared_ptr<Task> task)
{
    return !task->getUsed();
}

bool canBeThreaten(std::shared_ptr<Link> link)
{
    return link->getThreaten();
}


static void addLink(std::shared_ptr<const Link> link, std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links,
                    std::shared_ptr<Task> task)
{
    //we need to check if the link is not in the active list
    bool sameLink=false;
    for(int k=0; k<active_links->size();k++)
    {
        if(compareLinks(active_links->at(k)->first,link))
        {
            sameLink = true;
            break;
        }
    }
    if(!sameLink)
    {
      std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> >> tl(new std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> >(link,task));
      active_links->push_back(tl);

    }
}

static void addSteps(std::shared_ptr<Task> task, std::shared_ptr<std::vector< std::shared_ptr<StepTimed> > > active_list,
                     std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links)
{
    //TODO I can move this to some method and call it, as the task is created
    std::vector<std::pair<std::pair<size_t,float>,bool> > start_vector;
    std::vector<std::pair<std::shared_ptr<const Link>,bool> > link_vec;
    //add simplified orderings to the task
    if (task->getStartVector().empty()) //first run
    {
        //check ordering of the actions
        std::map<size_t, float> start_times;
        std::map<size_t, float> end_times;

        task->getPlan()->orderings().schedule(start_times, end_times);

        for(std::map<size_t, float>::const_iterator it = start_times.begin();
            it != start_times.end(); ++it)
        {
            std::pair<size_t, float> pair(it->first, it->second);
            std::pair<std::pair<size_t, float>, bool> pair2(pair,false);
            start_vector.push_back(pair2);
        }

        std::sort(start_vector.begin(),start_vector.end(),compareSF);
        task->setStartVector(start_vector);
    }

    const Plan * plan = task->getPlan();


    //add simplified links to the task
    if(task->getLinksVector().empty()) //first run
    {

        for (const Chain<Link>* sc = plan->links(); sc != NULL; sc = sc->tail)
        {
            std::stringstream ss;
            std::ostream &os(ss);

            sc->head.condition().print(os,sc->head.to_id(), *task->getPlan()->bindings_anytime());
            std::string action = ss.str();
            size_t index;
            index = action.find("(");

            if(index<std::numeric_limits<std::size_t>::max())
                action = action.substr(index,action.size());

           if(std::find(current_state[task->getDomain()].begin(),current_state[task->getDomain()].end(),action) != current_state[task->getDomain()].end()) //something was found
           {
             link_vec.push_back(std::pair<std::shared_ptr<const Link>,bool>(std::shared_ptr<const Link>(new Link(sc->head, task->getID())),true));
             sc->head.condition().print(os,sc->head.to_id(),*task->getPlan()->bindings_anytime());

           }
           else
           {
             link_vec.push_back(std::pair<std::shared_ptr<const Link>,bool>(std::shared_ptr<const Link>(new Link(sc->head, task->getID())),false));
             sc->head.condition().print(os,sc->head.to_id(),*task->getPlan()->bindings_anytime());

           }

        }
        task->setLinksVector(link_vec);

    }


    std::vector<std::pair<std::pair<size_t,float>,bool> >::iterator it;
    std::vector<std::pair<std::pair<size_t,float>,bool> >::iterator it2;

    start_vector = task->getStartVector();
    //map between step IDS and indexes of start_vector
    std::map<size_t, int> start_map;
    for(int i=0; i< start_vector.size();i++)
    {
       start_map.insert(std::pair<size_t,int>(start_vector.at(i).first.first,i));
    }

    std::vector<size_t> ids; //ids to add this time
    link_vec = task->getLinksVector();

    it = std::find_if(start_vector .begin(),start_vector .end(),findUsed);

    int previousStep = -1;

    while(it != start_vector.end()) //we found some step
    {
        const Plan* plan = task->getPlan();
        size_t id = it->first.first;

        //TODO I commented out this during ECAI paper as I thought it breaks TMS,
        //I need to find out why I have added it in the first place and if it is still correct
        /*if(previousStep != -1)
        {
           //check if this step can be before or in parallel with the previous step
           if(plan->orderings().possibly_not_after(id, StepTime::AT_START,previousStep, StepTime::AT_END))
           //if yes - check with the action before, etc...
           {
               int indexB = start_map[previousStep];
               int superPreviousStep;
               for(int q=indexB;q>0;q--)
               {
                  if(!(plan->orderings().possibly_not_after(id, StepTime::AT_START,start_vector.at(q).first.first, StepTime::AT_END)))
                  {
                    superPreviousStep =   start_vector.at(q).first.first;
                  }
               }
               if(std::find(ids.begin(),ids.end(),superPreviousStep)==ids.end())//we havent found anything
               {
                  previousStep = id;
                  it = std::find_if(it+1,start_vector.end(),findUsed);
                  continue;
               }

           }
           else
           //TODO this shouldnt be in previous IDs but already merged
           //if not - is the previous step added? if yes, continue normally, if not, I cant add this step or any link with it
           {
               if(std::find(ids.begin(),ids.end(),previousStep)==ids.end())//we havent found anything
               {
                  previousStep = id;
                  it = std::find_if(it+1,start_vector.end(),findUsed);
                  continue;
               }
           }
        }*/

         //if the step is not in to_id link, we want to add it
        //else if the from_id  not used, skip it

        bool linkFound = false;
        for(int j=0; j < link_vec.size(); j++)
        {
            size_t toID = link_vec.at(j).first->to_id();
            size_t fromID = link_vec.at(j).first->from_id();
            std::stringstream ss;
            std::ostream &os(ss);

            link_vec.at(j).first->condition().print(os, link_vec.at(j).first->condition().id(), *plan->bindings_anytime());
            std::string conditionA = ss.str();

            if(( toID == id)&&(!link_vec.at(j).second))
            { //if the id is in link which is not yet satisfied

                if(fromID==0) //the first init action
                {

                    //add the Link
                    addLink(link_vec.at(j).first,active_links, task);
                }
                else
                {
                    //is the action fromID satisfied?
                    int indexL = start_map[fromID];
                    if(start_vector.at(indexL).second) //if the action is satisfied add the link
                    {
                        //add the Link
                        addLink(link_vec.at(j).first,active_links,task);
                    }
                    else
                    {
                        //dont add the Link as the action is not satisfied
                    }

                }
                linkFound = true;
                break; //we found a link, we dont have to search more
            }
        }
        if(!linkFound) //no link is violating the action, we can add it
        {
          ids.push_back(id);
        }
        //search for another action
        previousStep = id;
        it = std::find_if(it+1,start_vector.end(),findUsed);

    }
    task->setStartVector(start_vector);

    //check if all the actions are done, and links not leading to goal are done,
    //you want to add links leading to goal
    it = std::find_if(start_vector .begin(),start_vector .end(),findUsed);
    if(it==start_vector.end())
    {
        int unUsed = 0;
        for(int x=0;x<link_vec.size();x++)
        {

            //if it is not satisfied and it is not leading to the goal state
           if((!link_vec.at(x).second)&&(link_vec.at(x).first->to_id()!=Plan::GOAL_ID))
           {
               //TODO what happens with the link which are not satisfied but they are in middle??!
               std::cout << "we have some unsatisfied links";
               throw;
           }
           else if ((!link_vec.at(x).second)&&(link_vec.at(x).first->to_id()==Plan::GOAL_ID))
           {
               //add this link that it can be finally satisfied
               addLink(link_vec.at(x).first,active_links,task);
           }

        }

    }




    for (const Chain<Step>* sc = plan->steps(); sc != NULL; sc = sc->tail)
    {
      std::unique_ptr<Step> step_p(new Step(sc->head));

      std::vector<size_t>::iterator its;
      its = std::find(ids.begin(),ids.end(),step_p->id());
      if(its != ids.end())
         if(!compareSteps(active_list,*step_p.get() )) //add the step and the step is not yet in the active_list
          {
              ids.erase(its);
              Task * t= task.get();
              std::shared_ptr<StepTimed> s_p(new StepTimed(std::move(step_p), new Task(*t),0)); //0 = activelist
              active_list->push_back(s_p);
          }
      if(ids.empty()) //we added all steps
        break;
    }
    /*if(!ids.empty())
    {
        //in this case
    }*/
}

/*This method should be done*/
static void checkActiveActions(double init_time, std::shared_ptr<std::vector< std::shared_ptr<StepTimed> > > active_list,
                               std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links)
{

    for (int i=0; i< tasks->size();i++)
    {
       if (tasks->at(i)->getReleaseDate() <= init_time) //the time window for the tasks is opened
       {  

          addSteps(tasks->at(i),active_list,active_links);

       }
    }

}


//TODO how am I going to distinguish what to put to the current state (with different domains)
//maybe have current state for each domain...?

static std::string writeInitialState(std::string domain)
{

    std::string output="";
    for (int i=0;i<current_state[domain].size();i++)
    {
      output += "    ";
      output += current_state[domain].at(i);
      output += "\n";
    }
    output += ")\n";
    return output;
}

/*writing a temporal problem to the file*/
//should be finished
static std::vector<std::string> createTempProblem(Task * origin, std::string action)
{
    std::stringstream ss;
    std::ostream &os(ss);

    std::string problemName = origin->getProblem();

    size_t index = problemName.find("problem.pddl");

    std::string line;
    std::ofstream file_out;
    std::ifstream file_in;
    std::string filename = problemName.substr(0,int(index)) + "temp_problem.pddl\0";
    std::string probname;

    //splitting action if and, getting at end, over all away
    std::vector<size_t> indexes;
    std::vector<std::string> sub_actions;
    std::string sub_action;
    int skip_index;
    int index3;

    bool andF = false;
    int index2 = -1;


    //if the predicate has "not", it is saved, but I need to test it
    if(action.find("and") != std::string::npos) //and statement
    {
        andF = true;
        skip_index = 2; //skip the first bracket
        index3 = action.find("(",skip_index);
        //find all predicates
        while( index3 != std::string::npos) //something found
        {
            indexes.push_back(index3);
            skip_index = action.find(")",skip_index+1);
            skip_index++;  //there always two brackets, I need the second one
            sub_action = action.substr(index3,skip_index-index3+1); //those predicates can have "not"
            index3 = action.find("(",skip_index);

            std::string when = "at end";
            index2 = sub_action.find(when);
            if(index2 != std::string::npos) //something found
            {
                sub_actions.push_back(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1)); //-1 dont take last bracket
            }
            else
            {
                when = "over all";
                index2 = sub_action.find(when);
                if(index2 != std::string::npos) //something found
                {
                    sub_actions.push_back(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1)); //-1 dont take last bracket
                }
                else //none of them is there, we can just add it
                {
                    when ="";
                    index2 = -1;
                    sub_actions.push_back(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1)); //-1 dont take last bracket
                }

            }
        }
    }
    else
    {
      andF = false;
      index3 = action.find("("); //TODO deleted here num 1, does it break things?
      index2 = -1;
      if (index3 != std::string::npos)
      {
          std::string when = "over all";
          index2 = action.find(when);
          if(index2 != std::string::npos) //something found
          {
              sub_actions.push_back(action.substr(index2+when.size()+1,action.size()-1-index2-when.size()-1)); //-1 dont take last bracket
          }
          else
          {
              when = "at end";
              index2 = action.find(when);
              if(index2 != std::string::npos) //something found
              {
                  sub_actions.push_back(action.substr(index2+when.size()+1,action.size()-1-index2-when.size()-1)); //-1 dont take last bracket
              }
              else
              {
                  when = "";
                  index2 = -1;
                  sub_actions.push_back(action.substr(index2+when.size()+1,action.size()-1-index2-when.size())); // changed -1 took away - dont take last bracket
              }

          }

      }
    }

    file_out.open ((filename).c_str());

    //copying settings of the problem file
    file_in.open(problemName.c_str());
    int h = 0;
    if (file_in.is_open())
    {
        while ( getline (file_in,line) )
        {
           if (h==0) //first line
           {
               h++;
               line = line.substr(0,line.length()-1)+"_temp"+std::to_string(g_temp_prob) + ")";
               g_temp_prob++;
               probname = line;
           }
           if(line.find("(:init") == std::numeric_limits<std::size_t>::max()) //copy
             file_out << line << "\n";
           else
             break; //stop
        }
    }
    file_in.close();
    file_out << "(:init\n";
    file_out << writeInitialState(origin->getDomain());
    file_out << "(:goal (and\n";



    //step_p->getStep()->action().condition().print(os,step_p->getStep()->id(), *origin->getPlan()->bindings_anytime());

    //std::string action = ss.str();

    //index = action.find("(");

    //if(index<std::numeric_limits<std::size_t>::max())
    //    file_out << "    " << action.substr(index,action.size()) << "\n";
    for(int x=0;x<sub_actions.size();x++)
    {
      file_out<< "    "  << sub_actions.at(x) << "\n";
    }

    file_out << ")))\n";
    file_out.close();

    probname = probname.substr(17,probname.length()-1);
    probname = probname.substr(0,probname.length()-1)+"\0";

    std::vector<std::string> names;
    names.push_back(filename);
    names.push_back(probname);

    return names;
}

static void planTempTask(Task * origin, std::string action)
{
    std::vector<std::string> names = createTempProblem(origin, action);
    std::string problemName = names.at(0);


    std::shared_ptr<Task> temp(new Task(-1,origin->getReleaseDate(),origin->getDeadline(),origin->getDomain(),problemName,names.at(1)));
    char * word;

    word = new char[problemName.length()+1]; //+1 to copy also null char in the end
    std::strcpy(word,problemName.c_str());
    g_argv[g_argc-1] = word;


    word = new char[origin->getDomain().length()+1]; //+1 to copy also null char in the end
    std::strcpy(word,origin->getDomain().c_str());
    g_argv[g_argc-2] = word;

    temp->callPlanner(g_argc,g_argv);



    temp_tasks->push_back(temp);
}

/*return value:
 * 0 no extra things needed
 * 1 extra actions needed to satisfy condition
 * -1 plan not existing*/
static int checkLinks(std::shared_ptr<std::pair<std::shared_ptr<const Link>, std::shared_ptr<Task> > > link_p)
{


    //TODO what if the condition is AND?

    std::stringstream ss;
    std::ostream &os(ss);

    link_p->first->condition().print(os,link_p->first->to_id(), *link_p->second->getPlan()->bindings_anytime());
    std::string action = ss.str();
    size_t index;
    index = action.find("(");

    if(index<std::numeric_limits<std::size_t>::max())
        action = action.substr(index,action.size());

    std::string domain = link_p->second->getDomain();

    if(std::find(current_state[domain].begin(),current_state[domain].end(),action) != current_state[domain].end()) //something was found
    {
        //TODO test the empty pointer
        temp_tasks->push_back(std::shared_ptr<Task>()); // empty task, to keep correct order
        return 0; //we do not need add anything
    }
    else
    {
        planTempTask(link_p->second.get(),action);
        //get the last temp tasks -> just added
        if(temp_tasks->at(temp_tasks->size()-1)->getPlan()!=NULL)
        {
            return 1;
        }
        else
            return -1; //plan was not found

    }
}


/*the string action contains the condition to be checked
  the when reffers to at start or at end
  domain is domain where to test predicate*/
static int areConditionsSatisfiedNow(std::string action, std::string when, std::string domain)
{
    std::vector<size_t> indexes;
    std::vector<std::string> sub_actions;
    std::string sub_action;
    int skip_index;
    int index;

    bool andF = false;
    int index2 = -1;


    //if the predicate has "not", it is saved, but I need to test it
    if(action.find("and") != std::string::npos) //and statement
    {
        andF = true;
        skip_index = 2; //skip the first bracket
        index = action.find("(",skip_index);
        //find all predicates
        while( index != std::string::npos) //something found
        {
            indexes.push_back(index);
            skip_index = action.find(")",skip_index+1);
            skip_index++;  //there always two brackets, I need the second one
            sub_action = action.substr(index,skip_index-index+1); //those predicates can have "not"
            index = action.find("(",skip_index);
            //subaction contains "at end" or over all
            if (when == "") //it is at start
            {
              if((sub_action.find("at end")==std::string::npos)&&(sub_action.find("over all")==std::string::npos))
              //it wasnt find none of those
              {
                  index2 = -1;
                  sub_actions.push_back(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1)); //-1 dont take last bracket
              }
              else
              {
                  //we found at end or overall, skip it
                  continue;
              }

            }
            else
                index2 = sub_action.find(when);
            if(index2 != std::string::npos) //something found
            {
                sub_actions.push_back(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1)); //-1 dont take last bracket
            }
        }
    }
    else
    {
      andF = false;
      index = action.find("("); //TODO deleted here num 1, does it break things?
      index2 = -1;
      if (index != std::string::npos)
      {
          if (when == "") //it is at start
          {
            if((action.find("at end")==std::string::npos)&&(action.find("over all")==std::string::npos))
            //it wasnt find none of those
            {
                index2 = -1;
                sub_actions.push_back(action.substr(index2+when.size()+1,action.size()-1-index2-when.size())); // changed -1 took away - dont take last bracket
            }
            else
            {
                //we found at end, over all when we are interested just in "at start" - skip it
                index2 = -1;
            }

          }
          else
              index2 = action.find(when);
          if(index2 != std::string::npos) //something found
          {
              sub_actions.push_back(action.substr(index2+when.size()+1,action.size()-1-index2-when.size()-1)); //-1 dont take last bracket
          }

      }
    }

    int predicateSatisfied = 1;
    for(unsigned int j=0;j<sub_actions.size();j++)
    {
        int index_c = std::distance(current_state[domain].begin(),std::find(current_state[domain].begin(),current_state[domain].end(),sub_actions.at(j)));

        if (index_c == current_state[domain].size()) //nothing found
        {
          predicateSatisfied*= 0; //this goal is not yet satisfied
          break; //we do not have to check others
        }
    }
    return predicateSatisfied;
}

/*return value:
 * 0 no extra things needed
 * 1 extra actions needed to satisfy condition
 * -1 plan not existing*/
static int checkPreconditions(std::shared_ptr<StepTimed> step_p)
{

    std::stringstream ss;
    std::ostream &os(ss);
    step_p->getStep()->action().condition().print(os,step_p->getStep()->id(), *step_p->getTask()->getPlan()->bindings_anytime());
    std::string action = ss.str();
    std::string domain = step_p->getTask()->getDomain();

    //TODO I should check also condition at end and over all and actually used them for orderings
    //empty string for "at start"
    if (( areConditionsSatisfiedNow(action,"", domain) == 1)&&( areConditionsSatisfiedNow(action,"over all", domain) == 1))
    {
        temp_tasks->push_back(std::shared_ptr<Task>()); // empty task, to keep correct order
        return 0; //we do not need add anything
    }
    else //not satisfied, we need to plan
    {
        planTempTask(step_p->getTask(),action);

        if(temp_tasks->at(temp_tasks->size()-1)->getPlan()!=NULL)
        //if(step_p->getTask()->getPlan() != NULL)
          return 1;
        else
          return -1;
    }

   /*size_t index;
    index = action.find("(");

    if(index<std::numeric_limits<std::size_t>::max())
        action = action.substr(index,action.size());

    index = action.find("(at start ");
    if(index<std::numeric_limits<std::size_t>::max())
    {
       action = action.substr(index+10,action.size()-(index+10)-1);
    }

    else
    {
        index = action.find("(at end ");
        if(index<std::numeric_limits<std::size_t>::max())
        {
           action = action.substr(index+8,action.size()-(index+8)-1);
        }
        else
        {
           index = action.find("(over all ");
           if(index<std::numeric_limits<std::size_t>::max())
           {
              action = action.substr(index+10,action.size()-(index+10)-1);
           }
           else
           {
               //no special time limitations
           }
        }

    }





    //TODO zde jsem skoncila - condition mohou byt "over all", "start..." atd
    if(std::find(current_state[domain].begin(),current_state[domain].end(),action) != current_state[domain].end()) //something was found
    {
        //TODO test the empty pointer
        temp_tasks->push_back(std::shared_ptr<Task>()); // empty task, to keep correct order
        return false; //we do not need add anything
    }
    else
    {
        planTempTask(step_p->getTask(),action);
        return true;
    }*/
}


static int checkLiteral(std::shared_ptr<FinalPlan> realPlan,const Literal * lit, size_t active_id, size_t lit_id,const Bindings * bind)
{
    std::vector<std::shared_ptr<Link> > * vecL = realPlan->getLinks(); //dont delete thhis pointer as it is not owner

    std::vector<std::shared_ptr<Link> >::iterator it = std::find_if(vecL->begin(), vecL->end(),canBeThreaten);

    int notThreating = 1;
    while (it != vecL->end()) //we found some link which might be threaten
    {
        //TODO do I need this If now?
        //if((*it)->to_id() == active_id) //if active_id is different than -1, it is from not finished action
        //this makes sure that action doesnt threat itself :)
        //{
           //as the action is finished now, the link is not threaten anymore
        //   realPlan->changeLink(std::distance(vecL->begin(),it),false);
        //   break;
        //}

        //find the step in the realPlan with ID = to_id - but to_id is "global",

        std::shared_ptr<StepTimed> stepRealPlan = realPlan->getStep((*it)->to_id());
        if (stepRealPlan.get() == NULL) //step with such an id hasnt been found
        {
          std::cout << "ERROR: the step where the link leads was not found\n";
          throw;
        }

        char type1 = lit->type();
        char type2 = (*it).get()->condition().type();

        //if are both same type, they will not cause a threat

        std::unique_ptr<const Atom> at1;
        std::unique_ptr<const Negation> neg2;
        std::stringstream ss;
        std::ostream &os(ss);

        std::string ac1;
        std::string ac2;

        if((type1 == 'a')&&(type2 == 'n'))
        {
            at1.reset(dynamic_cast<const Atom*>(lit->clone()));
            neg2.reset(dynamic_cast<const Negation*>((*it).get()->condition().clone()));

            at1->print(os,lit_id, *bind);
            ac1 =ss.str();
            ss.str(std::string());

            neg2->print(os,stepRealPlan->getStep()->id(), *stepRealPlan->getTask()->getPlan()->bindings_anytime());
            ac2 =ss.str();
            int index = ac2.find("(",1); //in order to skip "not"
            if(index!= std::string::npos) //found
            {
                ac2 = ac2.substr(index,ac2.size()-index-1);
            }
            ss.str(std::string());

        }
        else if((type2 == 'a')&&(type1 == 'n'))
        {
            at1.reset(dynamic_cast<const Atom*>((*it).get()->condition().clone()));
            neg2.reset(dynamic_cast<const Negation*>(lit->clone()));

            at1->print(os,stepRealPlan->getStep()->id(), *stepRealPlan->getTask()->getPlan()->bindings_anytime());
            ac1 =ss.str();
            ss.str(std::string());

            neg2->print(os,lit_id, *bind);
            ac2 =ss.str();
            int index = ac2.find("(",1); //in order to skip "not"
            if(index!= std::string::npos) //found
            {
                ac2 = ac2.substr(index,ac2.size()-index-1);
            }
            ss.str(std::string());
        }
        else
        {
            it = std::find_if(it+1, vecL->end(),canBeThreaten);
            continue;
        }


        if (ac1 == ac2)
        {
          notThreating = 0;
          break;
        }
        //check other links
        it = std::find_if(it+1, vecL->end(),canBeThreaten);
     }

    return notThreating;

}

//TODO nevim kam to napsat - porovnani predicates v Atoms je ciste na ID a ne na jejich vyrazu, ktery se da vyprintit
//je to problem??


// VOE - I dont want to test the active_action, but the action which is going to be added in its plan
static bool threatsLinks(std::shared_ptr<FinalPlan> realPlan,
                         std::shared_ptr<std::vector< std::shared_ptr<StepTimed> > > active_list_p,
                         std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links,
                         int index)
{

    const Formula * condition;
    size_t active_id;
    FormulaList formList;
    if (index>=active_list_p->size()) //check comes from the links
    {
        condition= active_links->at(index-active_list_p->size())->first->condition().clone();
        active_id = -1; //just link
        return false; //link cannot threats another links, it is the action
    }
    else //check comes from action
    {
        //TODO zde jsem skoncila - nahrad condition effectama
        EffectList effL = active_list_p->at(index)->getStep()->action().effects();

        for(unsigned int i=0; i<effL.size();i++)
        {
            //clone all effect literals
            formList.push_back(effL.at(i)->literal().clone());
        }

        if(active_list_p->at(index)->getEndTime()!=-1) //end action
        {
            std::map< std::shared_ptr<StepTimed>, size_t>::iterator it = realPlan->unfinished_actions.find(active_list_p->at(index));
            if (it != realPlan->unfinished_actions.end()) //found something
            {
               active_id = it->second;
            }
        }
        else
        {
            active_id = -1; //TODO which id here? //active_list_p->at(index)->getStep()->id();
        }
    }


    int isFormulaSaved = 1;
    int iter = 0;



    FormulaList::iterator itf = formList.begin();


    while(itf < formList.end())
    {
        char typeOfFormula = (*itf)->type();
        switch(typeOfFormula)
        {
           case 'a':
           {
             std::unique_ptr<const Atom> at (dynamic_cast<const Atom*>(*itf));
             isFormulaSaved *= checkLiteral(realPlan,at.get(), active_id, active_list_p->at(index)->getStep()->id(), active_list_p->at(index)->getTask()->getPlan()->bindings_anytime());
             break;
           }
           case 'n':
           {
             std::unique_ptr<const Negation> neg (dynamic_cast<const Negation*>(*itf));
             isFormulaSaved *= checkLiteral(realPlan,neg.get(), active_id, active_list_p->at(index)->getStep()->id(), active_list_p->at(index)->getTask()->getPlan()->bindings_anytime());
             break;
           }
           case 'j':
           {
             std::unique_ptr<const Conjunction> conj (dynamic_cast<const Conjunction*>(*itf));
             FormulaList tempL = conj->conjuncts();
             for(int i = 0;i<tempL.size();i++)
             {
                 //need to create a new pointer
               formList.push_back( tempL.at(i)->clone());
             }
             break;
           }
           case 't':
           {
             std::unique_ptr<const TimedLiteral> tl (dynamic_cast<const TimedLiteral*>(*itf));
             formList.push_back(tl->literal().clone());
             break;
           }
           default:
           {
            std::cout << "this type of formula is not yet covered\n";
            throw;
            break;
           }
        }
        iter++;
        itf = formList.begin()+iter;//increase iterator
     }

    /*std::unique_ptr<const Conjunction> conj (dynamic_cast<const Conjunction*>(condition));
    if(conj.get()!=NULL) //we have conjunction
    {
       FormulaList formList = conj->conjuncts();
       isFormulaSaved = 1;
       for(int i=0;i<formList.size();i++)
       {
           std::unique_ptr<const Atom> at (dynamic_cast<const Atom*>(formList.at(i)));
           if(at.get()!=NULL)
           {
               isFormulaSaved *= checkLiteral(realPlan,at.get());
           }
           else
           {
               std::unique_ptr<const Negation> neg (dynamic_cast<const Negation*>(condition));
               if(neg.get()!=NULL)
               {
                   isFormulaSaved *= checkLiteral(realPlan,neg.get());
               }
               else
               {
                   std::cout << "assuming wrong type of formula\n";
                   throw;
               }
           }
       }
       if (isFormulaSaved == 1) //none literal breaks it
       {
           return  false;
       }
       else
           return true;
    }*/


    if (isFormulaSaved == 1)//none literal breaks it
       return false;
    else
       return true;
}



static std::shared_ptr<StepTimed> getAction(std::shared_ptr<FinalPlan> realPlan,
                                            std::shared_ptr<std::vector< std::shared_ptr<StepTimed> > > active_list_p, std::shared_ptr<StepTimed> backtrack_a,
                                              std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links,
                                            double * timeTaken)
{


    std::vector<float> time_requir;

    //TODO maybe just unique ptr on Task

    std::vector<int> precond_needed(active_list_p->size()+active_links->size());

    //check preconditions of the active actions
    for(int i=0; i<active_list_p->size(); i++)
    {
        //is it end action?
        if(active_list_p->at(i)->getEndTime() == *timeTaken) //end action is ready to be used
        {
            //delete temp tasks
            temp_tasks->clear();
           return active_list_p->at(i);
        }
        if((active_list_p->at(i)->getEndTime() > -1)&&( active_list_p->at(i)->getEndTime() < *timeTaken)) //end action is ready to be used
        {
            std::cout << "ERROR: missed deadline of an action\n";
            throw;
        }
        if(active_list_p->at(i)->getEndTime() == -1) //it is a start action
        {
          float action_dur = active_list_p->at(i)->getStep()->action().max_duration().value();
          precond_needed.at(i) = checkPreconditions(active_list_p->at(i));
          if (precond_needed.at(i)==1) //there is a new plan
          {
             time_requir.push_back(temp_tasks->at(i)->getPlan()->duration() + action_dur);
          }
          else if (precond_needed.at(i)==0) //nothing needed
          {
            time_requir.push_back(action_dur);
          }
          else //plan does not exits
          {
              time_requir.push_back(INT_MAX); // to show that this one is broken
          }
        }
        else
        { //the end effect doesnt require any preconditions
            temp_tasks->push_back(std::shared_ptr<Task>()); // add empty task to make indexes allright
            precond_needed.at(i) = 0;
            time_requir.push_back(INT_MAX); //we want this super big not be chosen before it can be

        }
    }
    //check how to satisfied active links
   for(int i=0;i<active_links->size();i++)
   {
       //LEnka commented this out, we want to plan for link as long as it exists, because
       //we might have longer plan to satisfied the link 6/4/2016
      /*if(active_links->at(i)->first->getMerged() == true) //link already used
      {
          temp_tasks->push_back(std::shared_ptr<Task>());
          precond_needed.at(active_list_p->size()+i) = -1; // to signal it has been used
          time_requir.push_back(INT_MAX);
      }*/
      //else
      //{
        precond_needed.at(active_list_p->size()+i) = checkLinks(active_links->at(i));
          if (precond_needed.at(active_list_p->size()+i)==1) //there is a new plan
          {
               time_requir.push_back(temp_tasks->at(active_list_p->size()+i)->getPlan()->duration());
          }
          else if(precond_needed.at(active_list_p->size()+i)==0) //no plan needed
          {
              time_requir.push_back(0);
          }
          else //plan not found
          {
              time_requir.push_back(INT_MAX);
          }
       //}
   }


    std::vector<float>::iterator min_value;
    int index;
    //TODO use backtrack info - I can always use only action with begger requir. than the one with backtrack info

    bool threatsFound = false;
    do{ //check if chosen action/link does not cause threat on the realPlan links
        if (backtrack_a.get() != NULL)
        {
            std::vector<float> time_requir_copy = time_requir;
            std::sort(time_requir_copy.begin(),time_requir_copy.end());
            //the backtracked action is always last one in the list
           int value = std::distance(time_requir_copy.begin(),std::find(time_requir_copy.begin(),time_requir_copy.end(),time_requir.at(time_requir.size()-1))+1); // +1 to get iterator on the next item
            if(value == time_requir_copy.size())
            {
                std::cout<< "plans cannot be merged\n";
                throw;
            }
             min_value= std::find(time_requir.begin(),time_requir.end(),time_requir_copy.at(value));
        }
        else
        {
            min_value = std::min_element(time_requir.begin(),time_requir.end());
        }

        //if the action and link has same time_requir, do actions first, as the links always requires adding new actions
        float active_time_requir = *min_value;
        std::vector<size_t> all_indexes;
        std::vector<float>::iterator itTR = std::find(time_requir.begin(),time_requir.end(),active_time_requir);
        while(itTR != time_requir.end())//we found something
        {
            all_indexes.push_back(std::distance(time_requir.begin(),itTR));
            itTR = std::find(itTR+1,time_requir.end(),active_time_requir);
        }
        //sort indexes - smaller are from actions, bigger from links
        std::sort(all_indexes.begin(), all_indexes.end());

        index = all_indexes.at(0); //choose first one


       //sort of same logic as above
       if(time_requir.at(index) == INT_MAX) //the smallest value is error value, the rest will be also error values
       {
          //find if there is some precond_needed 0
           std::vector<int>::iterator it = std::find_if(precond_needed.begin(), precond_needed.end(),zerosPrec);

           std::vector<size_t> indexes_of_zeros;
           while(it != precond_needed.end()) //if we found one with zero, choose that one, otherwise the previously chosen stays
           {
              indexes_of_zeros.push_back(std::distance(precond_needed.begin(),it));
              it = std::find_if(it+1, precond_needed.end(),zerosPrec);
           }

           //if preconds are zero, and time_requis INT_MAX, it is only the END action
           if(indexes_of_zeros.size() != 0 )//we found some actions without precond
           {
               std::vector<std::pair<double, int> > deadlines;
               //we need to choose such an action which has earlier deadline
               for(unsigned int d=0;d<indexes_of_zeros.size();d++)
               {
                   deadlines.push_back(std::pair<double,int>(active_list_p->at(indexes_of_zeros.at(d))->getEndTime(),indexes_of_zeros.at(d)));
               }
               //sort them
               std::sort(deadlines.begin(),deadlines.end(), compareDeadlines);
               //choose the first -> the minimal one
               index = deadlines.at(0).second;

           }

       }


      if(precond_needed.at(index)==0)
      {
        //if this method returns true, we need to choose another action/link
        threatsFound =threatsLinks(realPlan,active_list_p,active_links, index);
      }
      else if (precond_needed.at(index)==1) //we are going to add some actions, test them!
      {
          std::shared_ptr< std::vector< std::shared_ptr<StepTimed> > > temp_active_list(new std::vector< std::shared_ptr<StepTimed> >() );
          std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > temp_active_links(new std::vector< std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > >() );
          std::shared_ptr<Task> tt(new Task(*temp_tasks->at(index).get()));
          addSteps(tt, temp_active_list, temp_active_links);
          threatsFound =threatsLinks(realPlan,temp_active_list,temp_active_links, 0); //index is 0 in this case, as we want to test the first adding (that is going to be chosen)
      }
     //change time_requir and precond_needed
     if(threatsFound)
     {
         time_requir.at(index) = INT_MAX;
         precond_needed.at(index) = -1; //to signal that this one is breaking links
     }
   } while(threatsFound);



    std::shared_ptr<StepTimed> active_action;

        if (precond_needed.at(index)==1)
        {
            //lenka commented out 6/4/2016
            //if(index>=active_list_p->size()) //action came from the link plan
            //{
            //    //we want to make that link satisfied
            //    active_links->at(index-active_list_p->size())->first->setMerged(true);

            //    //active_links->erase(active_links->begin()+index-active_list_p->size());
            //}
            int size_before = active_list_p->size();
            std::shared_ptr<Task> tt(new Task(*temp_tasks->at(index).get()));
            addSteps(tt, active_list_p, active_links);

            if (active_list_p->size() > size_before) //added some actions
            {

              //take the first added action
              active_action =active_list_p->at(size_before);
              //TODO test this

            }
            //TODO test this
            else //no action was added, maybe some link? but for that, we need to plan
            {
              active_action = NULL;
            }

            //delete all temp tasks as they will become invalid
            temp_tasks.reset(new std::vector<std::shared_ptr<Task> >());



            return active_action;
        }
        else if (precond_needed.at(index)==0) // no plan needed
        {
            if(time_requir.at(index) == INT_MAX) //this means that the end actions wants to be choosen, but the time is not yet ready
            {
               *timeTaken = active_list_p->at(index)->getEndTime();
                temp_tasks.reset(new std::vector<std::shared_ptr<Task> >());
                return active_list_p->at(index);
            }

            if(index < active_list_p->size()) //from actions
            {
              std::shared_ptr<StepTimed> active_action = active_list_p->at(index);
              temp_tasks->clear();
              return  active_action;
            }
            else //action comes from links, but there is no action, this shouldnt happen
            {
              std::cout<<"ERROR: Action comes from links\n";
              throw;
            }
        }
        else if (precond_needed.at(index)==-1) // chosen plan doesnt exists
        {
            active_action = NULL;
            temp_tasks.reset(new std::vector<std::shared_ptr<Task> >());
            return active_action;
        }

}

/*check the ordering constratins*/
//static bool checkConstraints()
//{

//}

/*this method creates links between steps of the realPlan*/
/*whichLink - "start" or "end" to choose which conditions should be checked*/
static std::vector<int> createLinks(std::shared_ptr<FinalPlan> realPlan, std::shared_ptr<StepTimed> active_action_p, std::string whichLink, size_t id_to)
{

    std::vector<int> from_ids; //return vector
    //link each condition of the active_action to its achiever
    std::stringstream ss;
    std::ostream &os(ss);

    const Formula * cond = active_action_p->getStep()->action().condition().clone();
    cond->print(os,active_action_p->getStep()->id(), *active_action_p->getTask()->getPlan()->bindings_anytime());
    std::string action = ss.str();

    std::vector<size_t> indexes;
   //sub action followed by the time
    std::vector<std::pair<std::string, FormulaTime> > sub_actions;
    std::string sub_action;
    int skip_index;
    int index;

    bool andF = false;
    int index2;
    std::string when;


    //if the predicate has "not", it is saved, but I need to test it
    if(action.find("and") != std::string::npos) //and statement
    {
        andF = true;
        skip_index = 2; //skip the first bracket
        index = action.find("(",skip_index);
        //find all predicates
        while( index != std::string::npos) //something found
        {
            indexes.push_back(index);
            skip_index = action.find(")",skip_index+1);
            skip_index++;  //there always two brackets, I need the second one
            sub_action = action.substr(index,skip_index-index+1); //those predicates can have "not"
            index = action.find("(",skip_index);
            //subaction contains "at end" or over all
            when = "at end";
            index2 = sub_action.find(when);
            if(index2!=std::string::npos)
            {
                sub_actions.push_back(std::pair<std::string, FormulaTime>(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1),FormulaTime::AT_END)); //-1 dont take last bracket
            }
            else
            {
                when = "over all";
                index2 = sub_action.find(when);
                if(index2!=std::string::npos)
                {
                    sub_actions.push_back(std::pair<std::string, FormulaTime>(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1),FormulaTime::OVER_ALL)); //-1 dont take last bracket
                }
                else
                {
                    when = "";
                    index2 = -1;
                    sub_actions.push_back(std::pair<std::string, FormulaTime>(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1),FormulaTime::AT_START)); //-1 dont take last bracket
                }
            }
        }
    }
    else
    {
      andF = false;
      sub_action = action;
      index = sub_action.find("("); //TODO deleted here num 1, does it break things?
      index2 = -1;
      if (index != std::string::npos)
      {
          when = "at end";
          index2 = sub_action.find(when);
          if(index2!=std::string::npos)
          {
              sub_actions.push_back(std::pair<std::string, FormulaTime>(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1),FormulaTime::AT_END)); //-1 dont take last bracket
          }
          else
          {
              when = "over all";
              index2 = sub_action.find(when);
              if(index2!=std::string::npos)
              {
                  sub_actions.push_back(std::pair<std::string, FormulaTime>(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()-1),FormulaTime::OVER_ALL)); //-1 dont take last bracket
              }
              else
              {
                  when = "";
                  index2 = -1;
                  sub_actions.push_back(std::pair<std::string, FormulaTime>(sub_action.substr(index2+when.size()+1,sub_action.size()-1-index2-when.size()),FormulaTime::AT_START)); //-1 dont take last bracket
              }
          }

      }
    }

    FormulaList formList;
    if(andF) //the condition is conjunction
    {
       std::unique_ptr<const Conjunction> conj (dynamic_cast<const Conjunction*>(cond));
       if(conj.get()!=NULL) //we have conjunction
       {
         formList = conj->conjuncts();

       }
       else
       {
           std::cout << "assuming we have conjunction, but it is not\n";
           throw;
       }
       if(formList.size() != sub_actions.size())
       {
           std::cout << "not compatible sizes\n";
           throw;
       }
    }
    else //just one
    {
        formList.push_back(cond);
    }



    for(unsigned int i = 0; i< sub_actions.size();i++)
    {

        //just add the links to the conditions, referring if we are anding start of the action or end
        if(((whichLink == "start")&&((sub_actions.at(i).second == FormulaTime::AT_START) || (sub_actions.at(i).second == FormulaTime::OVER_ALL))) ||
          ((whichLink == "end")&&((sub_actions.at(i).second == FormulaTime::AT_END)))) //not overall as it would add the link againss
        {
            std::string link_type;
            if(sub_actions.at(i).second == FormulaTime::AT_START)
                link_type = "start";
            else if (sub_actions.at(i).second == FormulaTime::OVER_ALL)
                link_type = "over all";
            else
                link_type = "end";

            std::map<std::string, std::pair<StepTime, int> >::iterator it;
            it = realPlan->achievers.find(sub_actions.at(i).first);
            if (it != realPlan->achievers.end()) // condition found
            {
                char typeOfFormula = formList.at(i)->type();
                switch(typeOfFormula)
                {
                   case 'a':
                   {
                    std::unique_ptr<const Atom> atom(dynamic_cast<const Atom*>(formList.at(i)));
                    //g_id is  the id of the sep in the realPlan
                     if(sub_actions.at(i).second == FormulaTime::OVER_ALL)  //might be threaten
                     {
                       std::shared_ptr<Link> lp(new Link(it->second.second, it->second.first,id_to , atom.get()->clone() ,sub_actions.at(i).second, true, link_type));
                       realPlan->addLink(lp);
                       from_ids.push_back(it->second.second);
                     }
                     else
                     {
                       std::shared_ptr<Link> lp(new Link(it->second.second, it->second.first,id_to , atom.get()->clone() ,sub_actions.at(i).second, false, link_type));
                       realPlan->addLink(lp);
                       from_ids.push_back(it->second.second);
                     }

                    break;
                   }
                case 'n':
                {
                 std::unique_ptr<const Negation> neg(dynamic_cast<const Negation*>(formList.at(i)));
                 //g_id is  the id of the sep in the realPlan
                  if(sub_actions.at(i).second == FormulaTime::OVER_ALL)  //might be threaten
                  {
                    std::shared_ptr<Link> lp(new Link(it->second.second, it->second.first,id_to , neg.get()->clone() ,sub_actions.at(i).second, true, link_type));
                    realPlan->addLink(lp);
                    from_ids.push_back(it->second.second);
                  }
                  else
                  {
                    std::shared_ptr<Link> lp(new Link(it->second.second, it->second.first,id_to , neg.get()->clone() ,sub_actions.at(i).second, false, link_type));
                    realPlan->addLink(lp);
                    from_ids.push_back(it->second.second);
                  }
                 break;
                }
                case 't':
                {
                 std::unique_ptr<const TimedLiteral> tl(dynamic_cast<const TimedLiteral*>(formList.at(i)));
                 //g_id is  the id of the sep in the realPlan
                  if(sub_actions.at(i).second == FormulaTime::OVER_ALL)  //might be threaten
                  {
                    std::shared_ptr<Link> lp(new Link(it->second.second, it->second.first,id_to , tl->literal().clone() ,sub_actions.at(i).second, true, link_type));
                    realPlan->addLink(lp);
                    from_ids.push_back(it->second.second);
                  }
                  else
                  {
                    std::shared_ptr<Link> lp(new Link(it->second.second, it->second.first,id_to , tl->literal().clone() ,sub_actions.at(i).second, false, link_type));
                    realPlan->addLink(lp);
                    from_ids.push_back(it->second.second);
                  }
                 break;
                }
                default:
                {
                    std::cout<< "adding link from not supported formula\n";
                    throw;
                    break;
                }

                }//end of sitch




            }//end of if which found an achiever
        }
    }

    return from_ids;
}

static void addAchiever(std::shared_ptr<FinalPlan> realPlan, std::string condition, Effect::EffectTime when, int id)
{
    StepTime s;

    if(when == AT_START)
    {
        s = StepTime::AT_START;
    }
    else
        s = StepTime::AT_END;

    //if condition is not yet in achievers, add it
    std::map<std::string,std::pair<StepTime, int> >::iterator it;
    it = realPlan->achievers.find(condition);
    if(it == realPlan->achievers.end()) //nothing found
    {
        realPlan->achievers[condition] = std::pair<StepTime, int>(s,id);
    }
    else //replace the id with the newer one
    {
        realPlan->achievers[condition] = std::pair<StepTime, int>(s,id);
    }
}

static void addDeleter(std::shared_ptr<FinalPlan> realPlan, std::string condition, Effect::EffectTime when, int id)
{
    StepTime s;

    if(when == AT_START)
    {
        s = StepTime::AT_START;
    }
    else
        s = StepTime::AT_END;

    //if condition is not yet in deleters, add it
    std::map<std::string,std::pair<StepTime, int> >::iterator it;
    it = realPlan->deleters.find(condition);
    if(it == realPlan->deleters.end()) //nothing found
    {
        realPlan->deleters[condition] = std::pair<StepTime, int>(s,id);
    }
    else //replace the id with the newer one
    {
        realPlan->deleters[condition] = std::pair<StepTime, int>(s,id);
    }
}

/*
 * type1 - effect type
 * ac1 - effect
 */
static std::vector<std::shared_ptr<Link>> isEffectThreatening(char type1, std::string ac1, std::shared_ptr<FinalPlan> realPlan, int active_id)
{

    std::vector<std::shared_ptr<Link>> ids_to;
    std::vector<std::shared_ptr<Link> > * links = realPlan->getLinks(); //dont delete this pointer, you dont own it

    for(int i=0;i<links->size();i++)
    {
        if(links->at(i)->to_id()==active_id) //the link was added by the same action what calls this method, skip it
        {
            continue;
        }
        char type2 = links->at(i)->condition().type();
        std::shared_ptr<StepTimed> stepRealPlan = realPlan->getStep(links->at(i)->to_id());
        if (stepRealPlan.get() == NULL) //step with such an id hasnt been found
        {
          std::cout << "ERROR: the step where the link leads was not found\n";
          throw;
        }

        //if are both same type, they will not cause a threat

        std::unique_ptr<const Atom> at1;
        std::unique_ptr<const Negation> neg2;
        std::stringstream ss;
        std::ostream &os(ss);

        std::string ac2;

        if((type1 == 'a')&&(type2 == 'n'))
        {
            neg2.reset(dynamic_cast<const Negation*>((links->at(i)->condition().clone())));
            ss.str(std::string());

            neg2->print(os,stepRealPlan->getStep()->id(), *stepRealPlan->getTask()->getPlan()->bindings_anytime());
            ac2 =ss.str();
            int index = ac2.find("(",1); //in order to skip "not"
            if(index!= std::string::npos) //found
            {
                ac2 = ac2.substr(index,ac2.size()-index-1);
            }
            ss.str(std::string());

        }
        else if((type2 == 'a')&&(type1 == 'n'))
        {
            at1.reset(dynamic_cast<const Atom*>((links->at(i)->condition().clone())));

            at1->print(os,stepRealPlan->getStep()->id(), *stepRealPlan->getTask()->getPlan()->bindings_anytime());
            ac2 =ss.str();
            ss.str(std::string());


            int index = ac1.find("(",1); //in order to skip "not"
            if(index!= std::string::npos) //found
            {
                ac1 = ac1.substr(index,ac1.size()-index-1);
            }
            ss.str(std::string());
        }
        if(ac1==ac2) //threating
        {
          ids_to.push_back(links->at(i)); //save the link
        }
     }
    return ids_to;

}

static bool checkOneTaskBeUsed(std::shared_ptr<Task> task)
{
    std::string domain = task->getDomain();
    std::stringstream ss;
    std::ostream &os(ss);
    const Problem* pr = Problem::find(task->getNameProblem());
    const Formula * goal = &pr->goal();
    goal->print(os,Plan::GOAL_ID,*task->getPlan()->bindings_anytime());

    std::string action = ss.str();

    //goal action has just "at end" conditions
    int goalSatisfied = areConditionsSatisfiedNow(action, "at end", domain);

    if(goalSatisfied == 1)
    {
        task->setUsed(true);
        return true;
    }
    return false;
}

static void checkTaskBeUsed()
{
   //task can be used even if not all his actions were used, check the condition
  //TODO take previous sentence into account when adding steps

  for(unsigned int i=0; i< tasks->size();i++)
  {
    checkOneTaskBeUsed(tasks->at(i));
  }
}

//TODO IMPORTANT - STEPTIME CAN BE ALSO AFTER START AND BEFORE END, I need to take this into accout

//we know that active_action can be merge, so do it
static bool mergeAction(std::shared_ptr<FinalPlan> realPlan, std::shared_ptr<StepTimed> active_action_p, double * timeTaken,
                        std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links,
                        std::shared_ptr< std::vector< std::shared_ptr<StepTimed> > > active_list)
{
    //here we know that the conditions are satisfied, we can merge effects

    //TODO fix orderings
    const TemporalOrderings * t = realPlan->getOrderings();
    std::unique_ptr<const TemporalOrderings> to;
    to.reset(new TemporalOrderings(*t));



    //first create links - create only those depending if the action is start, or end
    //end condiitons might be satisfied later by something

    size_t active_id;
    std::shared_ptr<Step> s;
    if(active_action_p->getEndTime()!=-1) //start action
    {
       //in order to change IDs of the final steps
       g_id ++; //increment id
       //TODO add step must contain also global id
       s.reset(new Step(g_id,active_action_p->getStep()->action()));
       realPlan->addStep(std::pair<std::shared_ptr<StepTimed>, std::pair<std::string, size_t> >(active_action_p,std::pair<std::string,size_t>("start",g_id)));
       realPlan->unfinished_actions[active_action_p] = g_id;
       std::vector<int> from_ids = createLinks(realPlan,active_action_p,"start",g_id);

       //dummy ordering start at 0
       to.reset(to->refine(Ordering(0,StepTime::AT_END,s->id(),StepTime::AT_START), *s.get() ));
       std::ostream &osg = std::cout;
       std::cout << "merged orderings before effects\n";
       to->print(osg);
       std::cout << "\n";
       //add the limitations based on added links
       for(int i=0; i<from_ids.size();i++)
       {
           //the previous action must be finished before the new can start
           //this is simple and TODO extend this
           //Ordering(s->id()-1,StepTime::AT_END,s->id(),StepTime::AT_START)
           to.reset(to->refine(Ordering(from_ids.at(i),StepTime::AT_END,s->id(),StepTime::AT_START), *s.get()));
       }
       active_id = g_id;


    }
    else //end action
    {

       std::map< std::shared_ptr<StepTimed>, size_t>::iterator it = realPlan->unfinished_actions.find(active_action_p);
       if (it != realPlan->unfinished_actions.end()) //found something
       {
          active_id = it->second;
       }
       else
       {
           std::cout << "Action is unfinished but it is not in the unfinished map\n";
           throw;
       }
       s.reset(new Step(active_id,active_action_p->getStep()->action()));
       realPlan->addStep(std::pair<std::shared_ptr<StepTimed>, std::pair<std::string, size_t> >(active_action_p,std::pair<std::string, size_t>("end", active_id)));
       realPlan->unfinished_actions.erase(it);
       std::vector<int> from_ids = createLinks(realPlan,active_action_p,"end", active_id);
       //dummy ordering start at 0
       to.reset(to->refine(Ordering(0,StepTime::AT_END,s->id(),StepTime::AT_START), *s.get() ));

       //LENKA 15/04 I think I dont need this here, I do it later in effects
       for(int i=0; i<from_ids.size();i++)
       {
           //the previous action must be finished before the new can start
           //this is simple and TODO extend this
           //Ordering(s->id()-1,StepTime::AT_END,s->id(),StepTime::AT_START)
           to.reset(to->refine(Ordering(from_ids.at(i),StepTime::AT_END,s->id(),StepTime::AT_START),  *s.get()));

       }


       //change threaten flag

       std::vector<std::shared_ptr<Link> > * vecL = realPlan->getLinks(); //dont delete thhis pointer as it is not owner

       std::vector<std::shared_ptr<Link> >::iterator itL = std::find_if(vecL->begin(), vecL->end(),canBeThreaten);

       while (itL != vecL->end())
       {
         if((*itL)->to_id() == active_id)
         {
            //as the action is finished now, the link is not threaten anymore
            realPlan->changeLink(std::distance(vecL->begin(),itL),false);
            break;
         }
         itL = std::find_if(itL+1, vecL->end(),canBeThreaten);
       }


    }
    std::ostream &osg = std::cout;
    std::cout << "merged orderings before effects\n";
    to->print(osg);
    std::cout << "\n";




    EffectList effL = active_action_p->getStep()->action().effects();
    size_t index;
    std::string domain = active_action_p->getTask()->getDomain();

    //IMPORTANT - canBeMerged set the endtime to -1 for the end actions
    //the start action would have the deadline of the action
    for (int i =0; i< effL.size();i ++)
    {
        /*use only those effect which rely if we are merge start or end of the action*/
        if((active_action_p->getEndTime()!=-1)&&(effL.at(i)->when() != Effect::AT_START))
        //we want start effects, but this is not one, do nothing
        {
            continue;
        }
        if((active_action_p->getEndTime()==-1)&&(effL.at(i)->when() != Effect::AT_END))
        //we want end effects, but this is not one, do nothing
        {
            continue;
        }



        //we got correct effect, put it to the current state
        std::stringstream ss;
        std::ostream &os(ss);


        effL.at(i)->literal().print(os,active_action_p->getStep()->id(), *active_action_p->getTask()->getPlan()->bindings_anytime());


        std::string action = ss.str();
        std::string condition;

        //TODO REALLY MUST TEST THE LOGIC OF ADDED ORDERINGS
        std::vector<std::shared_ptr<Link>> links = isEffectThreatening(effL.at(i)->literal().type(), action, realPlan, active_id);
        for(int q=0;q<links.size();q++) //we found some links which are threaten, order the new actions accordingly
        {
            if(links.at(q)->getType()=="start")
            {
                //28/04 I added this in order to make tms working, but it breaks drivelog, as
                //the action might threat the link
                //if(links.at(q)->getThreaten())
                //{
                  to.reset(to->refine(Ordering(links.at(q)->to_id(),StepTime::AT_START,active_id,StepTime::AT_START),  *s.get()));
                //}
            }
            else //overal and end type are same - the threatening action must be after end
            {
                //if(links.at(q)->getThreaten())
                //{
                  to.reset(to->refine(Ordering(links.at(q)->to_id(),StepTime::AT_END,active_id,StepTime::AT_START),  *s.get()));
                //}
            }

        }

        std::ostream &osg = std::cout;
        std::cout << "merged orderings after effects\n";
        to->print(osg);
        std::cout << "\n";

        bool neg = false;
        int index2;

        if(action.find("not") != std::string::npos) //negative
        {
            neg = true;
            index = action.find("(",2); //skip the first bracket
        }
        else
        {
          index = action.find("(");
        }


      if(index<std::numeric_limits<std::size_t>::max())
      {
        if(neg)
        {
            int index3 = action.find(")");
            action = action.substr(index,index3-index+1);//to ingore last bracket
        }
        else
            action = action.substr(index,action.size());

        //TODO I need to be really careful in the domain that between not and anything else
        //is a space
        std::string not_action = "(not "+action+")";
        std::vector<std::string> vec = current_state[active_action_p->getTask()->getDomain()];
        index2 = std::distance(vec.begin(),std::find(vec.begin(),vec.end(),action));


        if(index2 == vec.size()&&(!neg)) //nothign found
        {
            current_state[domain].push_back(action);
            addAchiever(realPlan, action, effL.at(i)->when(), active_id);
        }
        else if ((index2 < vec.size())&&(!neg)) //it is there, but it is not negated
        {// do nothing,
             addAchiever(realPlan, action, effL.at(i)->when(), active_id);
        }
        else if((index2 < vec.size())&&(neg)) //we want to delete it
        {
            current_state[domain].erase(current_state[domain].begin()+index2);
            // Lenka fix - we can't only deleted, we need to add the negation
            //otherwise it leads to undefined situations
            //TODO check if this logic is not broken at more places of the code
            //TODO should be not action be as achiever of not???
            current_state[domain].push_back("(not "+action+")");
            addDeleter(realPlan, action, effL.at(i)->when(), active_id);
        }
        else if ((index2 == vec.size())&&(neg)) //we need to add the neg
        {
            current_state[domain].push_back("(not "+action+")");
            addDeleter(realPlan, action, effL.at(i)->when(), active_id);
        }

        int index2_not = std::distance(vec.begin(),std::find(vec.begin(),vec.end(),not_action)); //try to find negation of the action

        if((index2_not < vec.size())&&(!neg)) //we found a negation in the current state, the action needs to be deleted
        {
            current_state[domain].erase(current_state[domain].begin()+index2_not);
            addAchiever(realPlan, action, effL.at(i)->when(), active_id);
        }

        //TODO test: what if the current state has not state and it should be deleted by added thing


      }

  }

  //save orderings back to the real plan
    realPlan->setOrderings(std::move(to));




    //deleting satisfied active_actions

    std::shared_ptr< std::vector< std::shared_ptr<StepTimed> > > satisActions(new std::vector< std::shared_ptr<StepTimed> >() );

    for(int i=0; i< active_list->size();i++)
    {

        std::string domain = active_list->at(i)->getTask()->getDomain();
        FormulaList formList;

        EffectList effL = active_list->at(i)->getStep()->action().effects();

        bool allEffects = true;
        for(unsigned int j=0; j<effL.size();j++)
        {
            std::stringstream ss;
            std::ostream &os(ss);
            //clone all effect literals
            effL.at(j)->literal().print(os,active_list->at(i)->getStep()->action().id(), *active_list->at(i)->getTask()->getPlan()->bindings_anytime());
            std::string action = ss.str();
            //TODO what time? probably at_start?
            if(!(areConditionsSatisfiedNow(action, "", domain)==1))
            {
                allEffects = false;
                break; //we wound at least one not satisfied, ie we can stop
            }
        }
        if (allEffects)//all effects are satisfied, we can delete the active action
        {
          if(active_list->at(i)->getEndTime() == -1) //it is start action, we can delete it
              //do not delete end action, as start is already merged
          {
            //here it deletes also the activeAction, so I can use it
            satisActions->push_back(active_list->at(i));
            active_list->erase(active_list->begin()+i);
            i--; //because the size has changed
          }
        }
    }

    //deleting satisfied active_links -

    for(int i=0; i< active_links->size();i++)
    {
        std::stringstream ss;
        std::ostream &os(ss);
        std::string domain = active_links->at(i)->second->getDomain();
        active_links->at(i)->first->condition().print(os,active_links->at(i)->first->to_id(), *active_links->at(i)->second->getPlan()->bindings_anytime());
        std::string action = ss.str();
        //TODO what time? probably at_start?
        if(areConditionsSatisfiedNow(action, "", domain)==1)
        {
            active_links->erase(active_links->begin()+i);
            i--; //because the size has changed
        }
    }


    for(int j=0;j<satisActions->size();j++)
    {
        if(satisActions->at(j)->getEndTime()==-1) //IMPORTANT - canBeMerged set the endtime to -1 for the end actions
            //the start action would have the deadline of the action
        {

            int taskId = satisActions->at(j)->getTask()->getID();
            //checking used actions from the tasks
            if (satisActions->at(j)->getTask()->getID() != -1) //action has come from origin tasks
            {
                //I need to get the original task!!
               std::vector<std::pair<std::pair<size_t,float>,bool> > sv = tasks->at(taskId)->getStartVector();

               for(int i =0; i<sv.size();i++)
               {
                   if(sv.at(i).first.first == satisActions->at(j)->getStep()->id())
                   {

                       sv.at(i).second = true;
                       tasks->at(taskId)->setStartVector(sv);
                       break;
                   }
               }

               //check is satisfied action hasnt satisfied also some link
               std::vector<std::pair<std::shared_ptr<const Link> ,bool> > links_vec=tasks->at(taskId)->getLinksVector();
               for(int k=0;k<links_vec.size();k++)
               {
                   //only if the satisfied action can satisfy new links
                   if(links_vec.at(k).first->from_id() == satisActions->at(j)->getStep()->id())
                   {
                       std::stringstream ss;
                       std::ostream &os(ss);
                       std::string domain = tasks->at(taskId)->getDomain();
                       links_vec.at(k).first->condition().print(os,links_vec.at(k).first->to_id(), *tasks->at(taskId)->getPlan()->bindings_anytime());
                       std::string action = ss.str();

                       //TODO what time? probably at_start?
                       if(areConditionsSatisfiedNow(action, "", domain)==1)
                       {
                           //if the link is to the goal, it can become satisfied, only if the task is satisfied
                           //not half way
                           if((links_vec.at(k).first->from_id()==0)&&(links_vec.at(k).first->to_id() == Plan::GOAL_ID))
                           {
                               if(checkOneTaskBeUsed(tasks->at(taskId)))
                               {
                                   links_vec.at(k).second = true;
                               }
                           }
                           else
                           {
                             links_vec.at(k).second = true;
                           }
                       }
                   }
               }
               tasks->at(taskId)->setLinksVector(links_vec);
            }
       }
    }

    return true;
}

static bool canBeMerged(std::shared_ptr<FinalPlan> realPlan, std::shared_ptr<StepTimed> active_action_p, double * timeTaken,
                        std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links)
{


    if(active_action_p == NULL) //there is none chosen action, but we still have things to merge
    {
        return false;
    }

        //TODO chechking deadlines of tasks
    if((active_action_p->getStep()->action().max_duration().value()+*timeTaken)>active_action_p->getTask()->getDeadline())
    {
        return false; //it is over a deadline
    }
    else
    {


        //TODO check constraints

        /*if(checkConstraints())
        {
            std::vector<int> row_c(mergedPlan->size(),-1); //many int with value -1
            row_c.push_back(2); // the last value is with the same action, thus 2
            constraints.push_back(row_c);
        }
        else
        {
            return false;
        }*/

        std::string domain = active_action_p->getTask()->getDomain();
        std::stringstream ss1;
        std::ostream &os2(ss1);

        /*before starting to merge, check if the conditions of the actions are really satisfied*/
        active_action_p->getStep()->action().condition().print(os2,active_action_p->getStep()->id(), *active_action_p->getTask()->getPlan()->bindings_anytime());

        std::string condition = ss1.str();
        if(active_action_p->getEndTime()==-1) //at start action - pass an empty string, as the stupid timed literal is not using at start
        {
          if (areConditionsSatisfiedNow(condition, "", domain)!=1)
          {
            return false;
          }
          //we need to test also over all conditions, as they must be true over all action
          if (areConditionsSatisfiedNow(condition, "over all", domain)!=1)
          {
            return false;
          }
        }
        else //at end action
        {
          if (areConditionsSatisfiedNow(condition, "at end", domain)!=1)
          {
            return false;
          }
          //we need to test also over all conditions, as they must be true over all action
          if (areConditionsSatisfiedNow(condition, "over all", domain)!=1)
          {
            return false;
          }
        }


      if(active_action_p->getEndTime()==-1) //start action
      {
          //we want to add "end" actions to the end_list, ha easier - just set the endtime and not delete it
          if((active_action_p->getStep()->action().max_duration().value()+*timeTaken)>active_action_p->getTask()->getDeadline())
          {
              return false; //it is over a deadline
          }
          active_action_p->setEndTime((active_action_p->getStep()->action().max_duration().value()+*timeTaken));
          //timeTaken hasnot been changed, because start action doesnt take anything
      }
      else //it is end action
      {
          if(*timeTaken != active_action_p->getEndTime())
          {
              std::cout << "wrong time to merge end effect\n";
              throw;
          }
          //we can set endTime to -1 again, that the action is deleted
          active_action_p->setEndTime(-1);
          //timeTaken will be set by some external power :)

      }

    }

    return true;

}

static void backtrack(std::shared_ptr< std::vector< std::shared_ptr<StepTimed> > > active_list,
                      std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links,
                      double * timeTaken)
{
    std::cout << "in backtrack\n";
    throw;
    /*std::shared_ptr<StepTimed> active_action_p = mergedPlan->at(mergedPlan->size()-1);

    *timeTaken = *timeTaken -active_action_p->getStep()->action().max_duration().value();


    std::string domain = active_action_p->getTask()->getDomain();
    EffectList effL = active_action_p->getStep()->action().effects();
    size_t index;

    for (int i =0; i< effL.size();i ++)
    {
        std::stringstream ss;
        std::ostream &os(ss);

        effL.at(i)->literal().print(os,active_action_p->getStep()->id(), *active_action_p->getTask()->getPlan()->bindings_anytime());

        std::string action = ss.str();

        bool neg = false;
        int index2;

        if(action.find("not") != std::string::npos) //negative
        {
            neg = true;
            index = action.find("(",2); //skip the first bracket
        }
        else
        {
          index = action.find("(");
        }


      if(index<std::numeric_limits<std::size_t>::max())
      {
        if(neg)
        {
            int index3 = action.find(")");
            action = action.substr(index,index3-index+1);//to ingore last bracket
        }
        else
            action = action.substr(index,action.size());

        std::string not_action = "(not"+action+")";
        std::vector<std::string> vec = current_state[domain];
        index2 = std::distance(vec.begin(),std::find(vec.begin(),vec.end(),action));


        //reverse logic - we want to delete all effects from the current state
        //TODO - issue, what if some effect was there and not added by an action
        if ((index2 < vec.size())&&(!neg)) //delete
        {
            current_state[domain].erase(current_state[domain].begin()+index2);
        }
        else if((index2 < vec.size())&&(neg)) //should happen
        {
           std::cout << "ERROR\n";
           throw;
        }
        else if(index2 == vec.size()&&(neg)) //we want to add it in normal way
        {
            current_state[domain].push_back(action);
        }
        else if(index2 == vec.size()&&(!neg)) //we want to add negated
        {
            current_state[domain].push_back("(not"+action+")");
        }


        //TODO do I need this?
        /*int index2_not = std::distance(vec.begin(),std::find(vec.begin(),vec.end(),not_action)); //try to find negation of the action

        if((index2_not < vec.size())&&(!neg)) //we found a negation in the current state, the action needs to be deleted
        {
            current_state[domain].erase(current_state[domain].begin()+index2_not);
        }*/
      /*}


  }//end effects


    //in the revert current state, the active_actio_p should be applicable
    std::stringstream ss;
    std::ostream &os(ss);
    active_action_p->getStep()->action().condition().print(os,active_action_p->getStep()->id(), *active_action_p->getTask()->getPlan()->bindings_anytime());
    std::string action = ss.str();

    bool neg = false;
    int index2;

    if(action.find("not") != std::string::npos) //negative
    {
        neg = true;
        index = action.find("(",2); //skip the first bracket
    }
    else
    {
      index = action.find("(");
    }


  if(index<std::numeric_limits<std::size_t>::max())
  {
    if(neg)
    {
        int index3 = action.find(")");
        action = action.substr(index,index3-index+1);//to ingore last bracket
    }
    else
        action = action.substr(index,action.size());


    int index_c = std::distance(current_state[domain].begin(),std::find(current_state[domain].begin(),current_state[domain].end(),action));

    if (index_c == current_state[domain].size())
    {
        std::cout<< "ERROR in backtracking, invalid current state\n";
        throw;
    }
    else
    {
        active_action_p->setMerged(0);
        active_action_p->setBacktrack(true);
        //TODO what if I will not add it back?
        active_list->push_back(active_action_p);
    }
  }*/

  //TODO I need to revert back addition of Links, and satisfied actions

}



static void merging(double init_time,std::shared_ptr<FinalPlan> realPlan)
{

    int numUnUsed = 0;
    double smallestRelease;
    std::shared_ptr< std::vector< std::shared_ptr<StepTimed> > > active_list(new std::vector< std::shared_ptr<StepTimed> >() );
    //std::pair<std::shared_ptr(const Link), std::shared_ptr(Task)> plt;
    std::shared_ptr<std::vector<std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > > > active_links(new std::vector< std::shared_ptr<std::pair<std::shared_ptr<const Link>,std::shared_ptr<Task> > > >() );
    bool success;

    if(tasks->size()<=0)
    {
        std::cout << "no tasks\n";
        return;
    }
    //take any problem to initialise mergedPlan
    //const Problem* pr = Problem::find(tasks->at(0)->getNameProblem());
    //const Problem& problem = *pr;

    //std::shared_ptr<const Plan> realPlan2(Plan::make_initial_plan(problem));



   //this could be done smarter
    for(int i=0; i<tasks->size();i++)
    {
        if (i == 0)
            smallestRelease = tasks->at(i)->getReleaseDate(); //initialise

        if (!(tasks->at(i)->getUsed()))
        {
          numUnUsed++;

          if (tasks->at(i)->getReleaseDate()<smallestRelease)
          {
              smallestRelease = tasks->at(i)->getReleaseDate();
          }
        }
    }


    int run =0;
    //in domains without release dates this loop should be done just once
    while (std::find_if(tasks->begin(), tasks->end(),taskUnused) < tasks->end()) // some tasks plans are still unsused
    {
        if(run>0)
        {
            std::cout << "running while loop moretimes\n";
            throw;
        }
        run++;


        checkActiveActions(init_time, active_list,active_links);

        while ((active_list->size()==0)&&(active_links->size()==0)) //no time window is opened
        {
          init_time = smallestRelease;

          checkActiveActions(init_time, active_list,active_links);
        }

        int active_size = active_list->size() + active_links->size();
        std::shared_ptr<StepTimed> backtrack_a (NULL);
        while(active_size!=0)
        {

          std::shared_ptr<StepTimed> active_action_p;
          do{
              active_action_p = getAction(realPlan,active_list,backtrack_a,active_links,&init_time);
          } while(active_action_p == NULL);

          success = canBeMerged(realPlan,active_action_p,&init_time,active_links);

          if(success)
          {
              std::stringstream ss;
              std::ostream &os(ss);
              active_action_p->getStep()->action().print(os,active_action_p->getStep()->id(), *active_action_p->getTask()->getPlan()->bindings_anytime());
              std::string action = ss.str();
              std::cout << "Merged action: " << action;
              if(active_action_p->getEndTime() == -1)
                  std::cout << " end\n";
              else
                  std::cout << " start\n";

              //active_action_p->getStep()->action().condition().print(os,active_action_p->getStep()->id(), *active_action_p->getTask()->getPlan()->bindings_anytime());
              //action = ss.str();
              //std::cout << "condition" << action << "\n";

              mergeAction(realPlan,active_action_p,&init_time,active_links,active_list);
              if(active_action_p->getEndTime() ==-1) //it can be deleted
              {
                 //int ind_act = std::distance(active_list->begin(),std::find(active_list->begin(),active_list->end(),active_action_p));
                 active_action_p.reset();
                 //the delete is now done in merge
                 //active_list->erase(active_list->begin()+ind_act);
              }
              checkActiveActions(init_time, active_list,active_links);
              active_size = active_list->size()+active_links->size();
              backtrack_a.reset();
              checkTaskBeUsed();
          }
          else
          {
              //TODO when to delete backtrack flag?
              //TODO backtracking
              backtrack(active_list,active_links, &init_time);
              //the backtrack action is last one
              backtrack_a = active_list->at(active_list->size()-1);
              //backtrack_a.reset();
          }

        }

    }

    //this print out is broken
    /*for(int i = 0; i<realPlan->size();i++)
    {
        const Action * a = &mergedPlan->at(i)->getStep()->action();
        std::ostream &os = std::cout;
        a->print(os,a->id(),*mergedPlan->at(i)->getTask()->getPlan()->bindings());
    }*/


}


static void readConfig(std::shared_ptr<Task> task,std::shared_ptr<FinalPlan> realPlan)
{

    //read the config and not add later those predicates, which were added in the relax planning graph
    std::string line;
    std::ifstream file_in;
    size_t index;
    index = task->getProblem().find("problem");

    std::string filename = task->getProblem().substr(0,int(index)) + "config";

    std::vector<std::string> not_be_added;

    file_in.open ((filename).c_str());

    if (file_in.is_open())
    {
        while ( getline (file_in,line) )
        {

            index = line.find("(");
            if(index<std::numeric_limits<std::size_t>::max())
            {
                line = line.substr(index,line.size()-index+1);
            }
            not_be_added.push_back(line);
        }
    }
    file_in.close();


    const Problem* pr = Problem::find(task->getNameProblem());

    GroundAction as = pr->init_action();
    EffectList effL = as.effects();



    //TODO get the actual name of domain
    std::string domain = task->getDomain();
    std::map<std::string,std::vector<std::string>>::iterator it;
    it = current_state.find(domain);
    if (it == current_state.end())
    {
        std::vector<std::string> init;
        current_state[domain] = init;
    }

    for(int x=0;x<effL.size();x++)
    {
        std::stringstream ss;
        std::ostream &os(ss);

        effL.at(x)->literal().print(os,as.id(), *task->getPlan()->bindings_anytime());

        std::string action = ss.str();

        index = action.find("(");

        if(index<std::numeric_limits<std::size_t>::max())
        {

            action = action.substr(index,action.size());
            //check if the action is not in the lines not be added
            //action is not found, we can add it
            if(std::find(not_be_added.begin(), not_be_added.end(),action)==not_be_added.end())
            {
                //check if it is not already in the current_state
               if(std::find(current_state[domain].begin(),current_state[domain].end(),action) == current_state[domain].end())
               {
                 current_state[domain].push_back(action);
                 if(action.find("not") == std::string::npos) //it is not negative
                   addAchiever(realPlan, action, effL.at(x)->when(), 0);
                 else
                   addDeleter(realPlan, action, effL.at(x)->when(), 0);
               }
            }

        }


    }


}




/* Cleanup function. */
static void cleanup() {
  Problem::clear();
  Domain::clear();
 }


//TODO how to call it with more problems
int main(int argc, char* argv[])
{
    atexit(cleanup);

    /*init CPU measure*/
    init();

    std::chrono::high_resolution_clock::time_point start, end;

    start = std::chrono::monotonic_clock::now();

    //read the config of the problem to solve
    char c;
    std::ifstream file_in;

    if(argc < 2)
    {
        std::cout << "you must specify config file of a problem to solve";
        return -1;
    }

    file_in.open(argv[1]);

    int num_items= 0;
    int num_lines = 0;
    int num_args = 0;
    std::string release = "";
    std::string deadline = "";
    std::string domain = "";
    std::string problem = "";
    std::string arguments = "";
    int num_tasks = 0;
    char ** args;

    char * word;

    std::string xal(argv[1]);
    std::cout << xal << "\n";
    if (file_in.is_open())
    {
        while ( file_in.get(c))
        {
            if(num_lines ==0) //store arguments
            {
                if (c == ';')
                {
                    num_items++;
                    if (num_items == 1)
                    {
                        num_args = std::stod(arguments);

                        args = new char*[num_args+2+2]; //+2 because of adding domain and problem file later +1 for .vhpop +1 for null pointer
                        arguments = "";
                    }
                    else
                    {
                        word = new char[arguments.length()];
                        std::strcpy(word,arguments.c_str());
                        args[num_items-2+1] = word;
                        arguments = "";
                    }
                }
                else if (c=='\n')
                {
                    num_lines++;
                    arguments ="";
                    num_items = 0;
                }
                else
                    arguments += c;
            }
            else
            {
                if(c == ';')
                    num_items++;
                else if (num_items ==0) //release_date
                    release += c;
                else if (num_items == 1)
                    deadline += c;
                else if (num_items == 2)
                    domain += c;
                else if (num_items == 3)
                    problem += c;
                else if (c == '\n')
                {
                    domain += "\0";
                    problem += "\0";
                    std::shared_ptr<Task> t(new Task(num_tasks,std::stod(release),std::stod(deadline),domain,problem));
                    tasks->push_back(t);
                    release = "";
                    deadline = "";
                    domain = "";
                    problem = "";
                    num_items = 0;
                    num_tasks++;
                }
            }

         }
    }
    file_in.close();



    std::shared_ptr<FinalPlan> realPlan(new FinalPlan());

    for (int i=0;i<num_tasks;i++)
    {


        //reading problem file to get the correct name of the problem
        std::ifstream file_prob;
        std::string line_p;

        file_prob.open(tasks->at(i)->getProblem().c_str());
        if (file_prob.is_open())
        {
            getline (file_prob,line_p); //get just first line
            std::string nameprob = line_p.substr(17,line_p.length());
            nameprob = nameprob.substr(0,nameprob.length()-1);
            tasks->at(i)->setNameProblem(nameprob);
        }
        file_prob.close();

        //------------


        args[0] = "./vhpop";

        std::string d= tasks->at(i)->getDomain();
        word = new char[d.length()+1];//+1 to copy also null char in the end
        std::strcpy(word,d.c_str());
        args[num_args+1] = word;

        std::string p = tasks->at(i)->getProblem();
        word = new char[p.length()+1]; //+1 to copy also null char in the end
        std::strcpy(word,p.c_str());
        args[num_args+2] = word;


        args[num_args+3] = NULL;
        tasks->at(i)->callPlanner(num_args+2+1, args);

        const Plan * pt= tasks->at(i)->getPlan();
        //std::cout << *pt << "\n";

        //TODO I have no idea what is this about

       /* std::ostream &osx = std::cout;
        bool repeat = true;
        for(const Chain<Step> * sc = pt->steps();sc != NULL; sc= sc->tail)
        {
            Step step = sc->head;
            const ActionSchema* as = dynamic_cast<const ActionSchema*>(&step.action());
            if(as != NULL)
            {
              const Formula * form = as->condition().clone();

              while(repeat)
              {
                char type = form->type();
                switch(type)
                {
                case 'a':
                {
                    std::unique_ptr<const Atom> a(dynamic_cast<const Atom*>(form));
                    int terms = a->arity();
                    for(int x =0; x<terms; x++)
                    {
                        const Term ter = a->term(x);
                        //const Term n_ter= Bindings::binding(ter, a->id());
                        //std::cout << "is object?" << n_ter.object() << "\n";
                    }
                    repeat = false;
                    break;
                }
                case 'n':
                {
                    std::unique_ptr<const Negation> n(dynamic_cast<const Negation*>(form));
                    repeat = false;
                    break;
                }
                case 't':
                {
                    std::unique_ptr<const TimedLiteral> t(dynamic_cast<const TimedLiteral*>(form));
                    form = t->literal().clone();
                    repeat = true;
                    break;
                }
                default:
                {
                    std::cout <<"wrong literal\n";
                    throw;
                }
                }
              }

            }
        }
*/


        readConfig(tasks->at(i),realPlan);

    }


    double init_time = 0.0;
    g_argc = num_args+3;
    g_argv = args;
    merging(init_time, realPlan);

    end = std::chrono::monotonic_clock::now();



    std::ostream &osx1 = std::cout;

    std::map<size_t, float> start_times;
    std::map<size_t, float> end_times;
    float makespan = realPlan->getOrderings()->getMakespan(start_times, end_times);
    std::cout << ";makespan: " << makespan;
    double final_time;
    for(int i=0; i<start_times.size();i++)
    {
        if(i>0)
        {
          std::cout << start_times[i] << ": "; //<< " " << end_times[i];

          std::shared_ptr<StepTimed> step = realPlan->getStep(i);
          step->getStep()->action().print(osx1,step->getStep()->action().id(),*step->getTask()->getPlan()->bindings());
        }
        final_time = end_times[i];
        std::cout << " [" << (end_times[i]-start_times[i]) << "]";
        std::cout << "\n";
    }




    std::cerr << ";virtual memory consumed " << getVirtualMemory()
              << std::endl;

    std::cerr << ";physical memory consumed " << getPhysicalMemory()
              << std::endl;

    std::cerr << ";CPU consumed " << getCurrentValueCPU()
              << std::endl;

    std::chrono::duration<double> dt = std::chrono::duration_cast<std::chrono::duration<double>>(end - start);
    std::cout << ";detail time: ";
    std::cout << dt.count();
    std::cout << "\n";



    delete [] args; //TODO not sure about this

    return 0;
}
