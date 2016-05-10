POMer - Partial Order Merging algorithm for AI planning

Steps to run:

* clone this repository
* cd POMer
* clone repositoty of modified VHPOP planner: https://github.com/mudrole1/vhpop
* follow instructions to compile just VHPOP
* use Qt creator to compile POMer
* while running POMer, it takes exactly one text file specifying the problem to be solved, see example-problem.txt, the structure of this file is:
* first line - configuration of vhpop planner, each parameter must be separated by ; 
* other lines - release datee of the task; deadline; path to domain; path to problem;
* specify one problem per one line
