//------------------------------
//guarding to avoid multiple including
#ifndef __TASK_H_INCLUDED__
#define __TASK_H_INCLUDED__


#include <string>
#include <vector>
#include <ostream>
#include <memory>

#include "vhpop/plans.h"
#include "vhpop/vhpop_callable.h"

class Task
{
  unsigned int id; //a number refering to the task
  double release_date;  //the time when the task can start
  double deadline;    //the time when the task needs to be finished
  double duration; //task duration, ignoring travel


  std::string domain_file;
  std::string problem_file; //filename
  std::string name_problem; //to save name of the problem from the file

  std::unique_ptr<const Plan> plan;
  bool plan_available;
  bool used;
  std::vector<std::pair<std::pair<size_t,float>,bool> > start_vector; //to save ordering steps
  std::vector<std::pair<std::shared_ptr<const Link> ,bool> > links_vector; //to save links

  Vhpop_callable v_callable;


  public:
  Task (unsigned int, double, double, std::string, std::string); //default priority = 1
  Task (unsigned int, double, double, std::string, std::string, std::string);
  Task (const Task&);


  unsigned int getID();
  double getReleaseDate();
  double getDeadline();
  double getDuration();
  std::string getDomain();
  std::string getProblem();
  void setNameProblem(std::string);
  std::string getNameProblem();
  void setUsed(bool);
  bool getUsed();
  std::vector<std::pair<std::pair<size_t,float>,bool> > getStartVector()
  {
      return start_vector;
  }
  void setStartVector(std::vector<std::pair<std::pair<size_t,float>,bool> > sv)
  {
      start_vector = sv;
  }
  std::vector<std::pair<std::shared_ptr<const Link> ,bool> > getLinksVector()
  {
      return links_vector;
  }
  void setLinksVector(std::vector<std::pair<std::shared_ptr<const Link> ,bool> > sv)
  {
      links_vector = sv;
  }


  std::vector<Step> steps;
  std::vector<const Action *> action;

  const Plan * getPlan();
  int callPlanner(int, char* []);
  Task& operator=(Task);

  friend std::ostream& operator<<(std::ostream&, const Task&);

};

#endif


