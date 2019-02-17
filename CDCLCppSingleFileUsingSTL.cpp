//============================================================================
// Name        : CDCLCppSingleFileUsingSTL.cpp
// Author      : Shaswata Jash
// Version     :
// Description : Implementation of CDCL Algorithm with additional enhancement of removeSingularPolarityVars
//               Input formula is accepted in CNF (Conjunctive Normal form) and is represented through DIMACS format.
//============================================================================

/******************************************************************************************************************************
 * Brief Description of Data-structure:
 * [1] Each clause is represented through unordered_map with key as clauseid (an unique number generated during initial parsing
 *     Dimacs parser) and value as literals. Further literals are arranged as unordered_set which ensures faster search as well as guaranteed unique literals.
 *     This is represented through 'clauseDB'.
 * [2] Further each literal maintains a reverse mapping to the clauseids where they are found. This data-structure is also maintained
 *     through unordered_map<int, unordered_set<int>> where key is literals and values are clause-ids. This is represented through 'umap'.
 *     We maintain this reverse mapping because as part of unit-clause propagation and splitting, while assigning a literal to one, we need to
 *     quickly able to find out where the particular literal is situated. It can be better understood by tracking deleteVarFromClause() function
 *     and its call from unitPropagate() and setVariableToTrue() functions. This also means any removal of clause-id has to update this reverse
 *     mapping too. Refer deleteClause() function and how umaps are updated from there.
 * [3] A dedicated list which maintains any unit-clause (represented through 'unitClause'). Further note that, when clauses from clauseDB is converted into unit-clause
 *     i.e. when it has only single element remaining, it is moved from clauseDB to unitClause. Additionally, 'conflictDetectorForUnitClause'
 *     is an unordered_set which helps to find out conflict during unit-clause propagation. Refer its usage in unitPropagate.
 * [4] satResult is a list which holds assignment result of the literals.
 *
 *****************************************************************************************************************************/

/****************************************************************************************************************************
 * Brief description of code-flow
 * runDPLLAlgo(bool isDebug, int recursionDepth) {
 *
 *   if (!unitPropagate(isDebug)) {
 *       return (false); //conflict detected
 *   }
 *
 *   if (clauseDB.empty() && unitClause.empty()) {
 *       return (true); //SAT
 *   }
 *
 *   bool lookAheadUnitProp = (!isLookAheadUnitPropStepEnabled) ? true : lookAheadUnitPropagate(isDebug);
 *   if (!lookAheadUnitProp) {
 *       return (false); //conflict detected
 *   }
 *
 *   removeSingularPolarityVars(isDebug);
 *
 *   if (clauseDB.empty()) {
 *       if (!unitClause.empty()) {
 *           if (isDebug) {
 *               cout << "Re-triggering unit clause reduction" << endl << std::flush;
 *           }
 *           return (unitPropagate(isDebug));
 *       }
 *       return (true); //SAT
 *   }
 *
 *   int splitVar = chooseSplitVarAccordingtoHeuristic(isDebug);
 *
 *   if (split(splitVar, isDebug, recursionDepth + 1)) {
 *       return (true);
 *   }else{
 *       if(clauseLearning){
 *           if(nonChronoBacktrackLevel != recursionDepth){
 *               return (false);
 *           }
 *           addLearnedClause(isDebug, recursionDepth);
 *           goto split_tag;
 *       }
 *   }
 *
 *   if (split(splitVar * -1, isDebug, recursionDepth + 1)) {
 *       return (true);
 *   } else{
 *       if(clauseLearning){
 *           if(nonChronoBacktrackLevel == recursionDepth){
 *               addLearnedClause(isDebug, recursionDepth);
 *               goto split_tag;
 *           }
 *       }
 *   }
 *
 *   return (false); //UNSAT
 *}

 ***************************************************************************************************************************/

/**********************************************************************************************************
 * Brief description of Heuristics Algo
 * There are mainly three heuristics algorithms -
 * MOMS: Maximum Occurrence of variable in Minimum size clauses [Refer:CDCLAlgo::momsHeuristic()]
 * BI_POLARITY_STAT: Heuristics based on count of both polarities of a particular variables (further choice of SUM, DIFF, PRODUCT and MAX)
 *                   [Refer : CDCLLAlgo::biPolarityHeuristic()]
 *********************************************************************************************************/
#include <iostream>
#include <fstream>
#include <stdexcept>
#include <cstring>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <list>
#include <chrono>
#include <cassert>
#include <algorithm>
#include <cstdlib>
using namespace std;

#include <bits/stdc++.h>
#include <dirent.h>

class Clause {
private:
    unordered_set<int> literals;
    int uniqueId = -1; //uninitialized
public:
    Clause() {
    }

    Clause(const Clause& c) {
        literals = c.literals;
        uniqueId = c.uniqueId;
    }

    void insertVar(int var) {
        literals.insert(var);
    }

    bool isPresent(int var) {
        return ((literals.find(var) == literals.end()) ? false : true);
    }

    bool isSingleVariableClause() {
        return ((1 == literals.size()) ? true : false);
    }

    bool isEmptyClause() {
        return (literals.empty());
    }

    int getVariablesListSize() {
        return (literals.size());
    }

    void deleteVar(int var) {
        literals.erase(var);
    }

    void setUniqueID(int id) {
        uniqueId = id;
    }

    int getUniqueID() {
        return (uniqueId);
    }

    int getUnitVar() {
        if (!isSingleVariableClause()) {
            throw std::logic_error("");
        }
        return (*(literals.begin()));
    }

    void fillWithVars(list<int>& vars) {
        vars.clear();
        unordered_set<int>::iterator itr;
        for (itr = literals.begin(); itr != literals.end(); itr++) {
            vars.push_back(*itr);
        }
    }

    void clear(){
        literals.clear();
    }
};

// ========================================== CDCLAlgo ========================

typedef enum HeuristicAlgo {
    MOMS, BI_POLARITY_STAT
} HeuristicAlgo;

typedef enum BiPolarityHeuristic {
    SUM, DIFF, PRODUCT, MAX, NONE
} BiPolarityHeuristic;

class VarAssignInfo {
public:
    int antecendentClause = -1;
    int level = -1;

    VarAssignInfo(){}

    VarAssignInfo(const VarAssignInfo& v) {
        antecendentClause = v.antecendentClause;
        level = v.level;
    }
};

class CDCLAlgo {
private:

    HeuristicAlgo algo;
    BiPolarityHeuristic typeOfBiPolarHeuristic;

    //For all the below three reference variable, data in them will be changed (majorly deleted but for unitClause, elements
    // can be added too) - thus caller of runDPLLAlgo() should rely sanctity of these variables after return from the functions.
    unordered_map<int, Clause>& clauseDB; //map of unique clause-id to actual clauses
    unordered_map<int, unordered_set<int>>& umap; //map of variable to list of clause-id (each clause is assigned unique id)
    unordered_map<int, int>& unitClause; //key = unitClause literal, value = original clause-id where it was present
    unordered_map<int, int> conflictDetectorForUnitClause; //key = unitClause literal, value = original clause-id where it was present

    unordered_map<int, unordered_map<int, VarAssignInfo>> literalAncedentHistory; //key = clauseid, value: <key = literal which going to set zero , value = {Ancedent literal, Ancedent level}
    int nonChronoBacktrackLevel;
    int lastLearnedClauseFromChild;
    int cdclLearnCount;
    bool clauseLearning;
    bool retractToHighestLevel;

    map<int,int> freeVarAssignHist; //key = level, value = assigned literal (due to usage of map, it is ordered on level)

    static unordered_map<int, Clause> originalClauseStorage;
    static int currentLearntClauseId;
    static int startIndexOfLearnedClause;

    list<int> satResult;

    //When isDirectionChoicePrioritizedAccordingToUnitClauseProp is true, intention is to trigger as much as possible reduction of clauses (not removal of clause)
    bool isDirectionChoicePrioritizedAccordingToUnitClauseProp;

    int momsHeuristic(bool isDebug) ;
    int biPolarityHeuristic(bool isDebug) const;

    int chooseSplitVarAccordingtoHeuristic(bool isDebug) {

        switch (algo) {
        case MOMS:
            return (momsHeuristic(isDebug));
        case BI_POLARITY_STAT:
            return (biPolarityHeuristic(isDebug));
        default:
            assert(false);
        }
        return (0);
    }

    void addClause(bool isDebug, Clause& c_from_global, unordered_set<int>& assignedLiterals){

        Clause c(c_from_global);

        list<int> listOfVars;
        c.fillWithVars(listOfVars);
        list<int>::iterator itv;
        for (itv = listOfVars.begin(); itv != listOfVars.end(); itv++) {
            if (assignedLiterals.find(*itv) != assignedLiterals.end()){
                if(isDebug){
                    cout << "Clause-id = " << c.getUniqueID() << " has assigned literal = " << *itv << endl;
                }
                return; //this clause must have been deleted as literal would have been assigned
            }else if(umap.find(*itv) == umap.end()){
                if(isDebug){
                    cout << "Clause-id = " << c.getUniqueID() << " has un-assigned literal = " << *itv << endl;
                }
                c.deleteVar(*itv);
            }
        }

        if(c.isEmptyClause()){
            if(isDebug){
                cout << "Clause-id = " << c.getUniqueID() << " has become empty " << endl;
            }
            return;
        }

        if(c.isSingleVariableClause()){
            unitClause[c.getUnitVar()] = c.getUniqueID();
            if(isDebug){
                cout << "Clause-id = " << c.getUniqueID() << " has become unit-clause " << endl;
            }
            return;
        }

        assert(clauseDB.find(c.getUniqueID()) == clauseDB.end());
        clauseDB[c.getUniqueID()] = c;
        c.fillWithVars(listOfVars);

        for (itv = listOfVars.begin(); itv != listOfVars.end(); itv++) {
            if(umap.find(*itv) != umap.end()){
                umap[*itv].insert(c.getUniqueID());
            }
        }
    }

    void deleteClause(int clauseSeqId) {

        if (clauseDB.find(clauseSeqId) == clauseDB.end()) {
            stringstream fmt;
            fmt << __FILE__ << ':' << __LINE__ << " No matching clauseid " << clauseSeqId << " found";
            throw logic_error(fmt.str());
        }
        Clause& affectedClause = clauseDB[clauseSeqId];

        list<int> vars;
        affectedClause.fillWithVars(vars);

        //remove reference of clauseid from affected variable
        list<int>::iterator iteratorForAffectedVars;
        list<int> deletableVarsFromUmap;
        for (iteratorForAffectedVars = vars.begin(); iteratorForAffectedVars != vars.end(); iteratorForAffectedVars++) {
            umap[*iteratorForAffectedVars].erase(clauseSeqId);
            if (0 == umap[*iteratorForAffectedVars].size()) {
                deletableVarsFromUmap.push_back(*iteratorForAffectedVars);
            }
        }
        for (iteratorForAffectedVars = deletableVarsFromUmap.begin();
                iteratorForAffectedVars != deletableVarsFromUmap.end(); iteratorForAffectedVars++) {
            if (umap.erase(*iteratorForAffectedVars) <= 0) {
                stringstream fmt;
                fmt << __FILE__ << ':' << __LINE__ << " variable= " << (*iteratorForAffectedVars)
                                << " cannot be erased from umap";
                throw std::logic_error(fmt.str());
            }
        }

        //now remove the clause-id itself
        clauseDB.erase(clauseSeqId);
    }

    Clause& deleteVarFromClause(int var, int clauseSeqId, int level, int antecendentClause) {
        Clause& affectedClause = clauseDB[clauseSeqId];
        affectedClause.deleteVar(var);
        umap[var].erase(clauseSeqId);
        if (0 == umap[var].size()) {
            if (umap.erase(var) <= 0) {
                stringstream fmt;
                fmt << __FILE__ << ':' << __LINE__ << " variable= " << (var) << " cannot be erased from umap";
                throw std::logic_error(fmt.str());
            }
        }

        VarAssignInfo v;
        v.level = level;
        v.antecendentClause = antecendentClause;
        literalAncedentHistory[clauseSeqId][var]=v;
        return (affectedClause);
    }

    static void printCurrentUnitClauseQueue(unordered_map<int, int>& unitClause);
    static void printDebugInfo(int recursionDepth, unordered_map<int, Clause>& clauseDB,
            unordered_map<int, int>& unitClause);
    static void printVarToClauseMapping(unordered_map<int, unordered_set<int>>& my_umap);
    void setVariableToTrue(int var, bool isDebug, int level);
    bool removeSingularPolarityVars(bool isDebug);
    bool unitPropagate(bool isDebug, int level);
    void learnConflictReason(int conflictedVar, int originatingClauseID1, int originatingClauseID2, bool isDebug);
    void addLearnedClauseFromChild(bool isDebug, int recusrsionDepth);
    bool split(int var, bool isDebug, int recursionDepth);

public:
    bool runCDCLAlgo(bool isDebug, int recursionDepth);

    list<int>& getSatResult() {
        return (satResult);
    }

    CDCLAlgo(HeuristicAlgo my_algo, BiPolarityHeuristic subType,
            bool directionPriorityTowardsMoreUnitClauseRed, bool cdcl, bool retractToHighest,
            unordered_map<int, Clause>& my_clauseDB, unordered_map<int, unordered_set<int>>& my_umap, unordered_map<int, int>& my_unitClause) :
                algo(my_algo), typeOfBiPolarHeuristic(subType),
                clauseDB(my_clauseDB), umap(my_umap), unitClause(my_unitClause),
                nonChronoBacktrackLevel(-1), lastLearnedClauseFromChild(-1), cdclLearnCount(0), clauseLearning(cdcl), retractToHighestLevel (retractToHighest),
                isDirectionChoicePrioritizedAccordingToUnitClauseProp(directionPriorityTowardsMoreUnitClauseRed) {
    }

    static void resetCDCL(){
        originalClauseStorage.clear();
        currentLearntClauseId = -1;
        startIndexOfLearnedClause = -1;
    }
};

unordered_map<int, Clause> CDCLAlgo::originalClauseStorage;
int CDCLAlgo::currentLearntClauseId = -1;
int CDCLAlgo::startIndexOfLearnedClause = -1;

void CDCLAlgo::printCurrentUnitClauseQueue(unordered_map<int, int>& my_unitClause) {
    unordered_map<int, int>::iterator singleClauseIt;
    if (my_unitClause.size() > 0) {
        cout << "[S:";
        for (singleClauseIt = my_unitClause.begin(); singleClauseIt != my_unitClause.end(); singleClauseIt++) {
            cout << singleClauseIt->first << ',';
        }
        cout << ']';
    }
}

void CDCLAlgo::printDebugInfo(int recursionDepth, unordered_map<int, Clause>& my_clauseDB,
        unordered_map<int, int>& my_unitClause) {
    cout << "[Depth=" << recursionDepth << "]";

    printCurrentUnitClauseQueue(my_unitClause);

    unordered_map<int, Clause>::iterator itr;
    for (itr = my_clauseDB.begin(); itr != my_clauseDB.end(); itr++) {
        cout << "[C" << itr->first << ':';
        list<int> vars;
        (itr->second).fillWithVars(vars);
        list<int>::iterator varsInClause;
        for (varsInClause = vars.begin(); varsInClause != vars.end(); varsInClause++) {
            cout << *varsInClause << ',';
        }
        cout << ']';
    }
    cout << endl << std::flush;
}

void CDCLAlgo::printVarToClauseMapping(unordered_map<int, unordered_set<int>>& my_umap) {
    unordered_map<int, unordered_set<int>>::iterator itr;
    for (itr = my_umap.begin(); itr != my_umap.end(); itr++) {
        cout << "[V" << itr->first << ':';

        if (0 == (itr->second).size()) {
            stringstream fmt;
            fmt << __FILE__ << ':' << __LINE__ << " variable= " << (itr->first)
                            << " has zero length clause list!!! in umap";
            throw std::logic_error(fmt.str());
        }

        unordered_set<int>::iterator clauseSqIt;
        for (clauseSqIt = (itr->second).begin(); clauseSqIt != (itr->second).end(); clauseSqIt++) {
            cout << *clauseSqIt << ',';
        }
        cout << ']';
    }
    cout << endl << std::flush;
}

void CDCLAlgo::setVariableToTrue(int var, bool isDebug, int level) {

    //The first check with respect to umap.find is very important , without that unnecessary blank element with complementUnitVar will be inserted in umap
    //It is important to note that we can landup into following scenarios where below mentioned checks are necessary
    //e.g. (x1+x2)*(x3*x2) suppose variable setting started (refer lookAheadUnitPropagate function) with !x1->!x3, !x1 will trigger a new unitVar = x2.
    //!x3 will ensure x2 as another unit var, but it will also remove reference to any clauseid corresponding to x2
    //Now finally when x2 is picked for unit var, it is not supposed to see any reference of x2 in umap

    if (umap.find(var) != umap.end()) {

        //Caution: do not use reference for listOfAffectedClauses. If we do so, we may land up in deleting from the same list
        //within deleteClause() which is being accessed (by reference) for iteration of affected clause
        unordered_set<int> listOfAffectedClauses = umap[var];
        unordered_set<int>::iterator iteratorForAffectedClauseIds;
        for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
                iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
            deleteClause(*iteratorForAffectedClauseIds);
        }
    }

    int complementUnitVar = var * -1;
    if (umap.find(complementUnitVar) != umap.end()) {

        unordered_set<int> listOfAffectedClauses = umap[complementUnitVar];
        unordered_set<int>::iterator iteratorForAffectedClauseIds;
        for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
                iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
            Clause& affectedClause = deleteVarFromClause(complementUnitVar, *iteratorForAffectedClauseIds, level, -1);//no antecedent clause as free variable

            if (affectedClause.isSingleVariableClause()) { //after deletion of var, the clause has now become unit-var
                int remainingVar = affectedClause.getUnitVar();
                unitClause[remainingVar] = affectedClause.getUniqueID();
                deleteClause(*iteratorForAffectedClauseIds);
            }
        }
    }
}

//MOMS heuristic
int CDCLAlgo::momsHeuristic(bool isDebug) {

    if(clauseLearning){

        for(int i=currentLearntClauseId; i>= startIndexOfLearnedClause; i--){ //pickup vars from recent one
            if(clauseDB.find(i) != clauseDB.end()){
                list<int> vars;
                clauseDB[i].fillWithVars(vars);
                list<int>::iterator it;

                for(it = vars.begin(); it != vars.end(); it ++){
                    assert(umap.find(*it) != umap.end());
                    assert(umap.find(*it * -1) != umap.end());
                    return (*it); //TODO: check for all remaining var assignment
                }
            }
        }
    }

    //STAGE1: First create map for size of clause to clause-id mapping
    map<int, list<int>> sizeToClauseIdMapping; //it will be default ordered in ascending (i.e. lower size clauses to higher ones)
    unordered_map<int, Clause>::iterator itr1;
    for (itr1 = clauseDB.begin(); itr1 != clauseDB.end(); itr1++) {
        sizeToClauseIdMapping[(itr1->second).getVariablesListSize()].push_back((itr1->second).getUniqueID());
    }

    map<int, list<int>>::iterator itr2;
    for (itr2 = sizeToClauseIdMapping.lower_bound(2); itr2 != sizeToClauseIdMapping.end(); itr2++) { //start iterate only from size 2
        list<int>& clauseids = itr2->second; //choose the list of clauses with lowest sizes ex. 2, 3 and so on
        if (isDebug) {
            list<int>::iterator ditr1;
            cout << "<MOMS> Clause-ids with min size of " << itr2->first << ':';
            for (ditr1 = clauseids.begin(); ditr1 != clauseids.end(); ditr1++) {
                cout << *ditr1 << ',';
            }
            cout << endl << std::flush;
        }

        //STAGE2: Now for each variables in lowest size clauses, find out variables with max freq
        //STAGE2.1 -> first create variables to freq map
        unordered_map<int, int> varToFreqCount;
        list<int>::iterator itr3;
        for (itr3 = clauseids.begin(); itr3 != clauseids.end(); itr3++) {
            //now iterate variables under specific clause-id to get the variable with maximum occurring
            Clause& c = clauseDB[*itr3];
            list<int> vars;
            c.fillWithVars(vars);
            list<int>::iterator itr4;
            for (itr4 = vars.begin(); itr4 != vars.end(); itr4++) {
                /*
                 * Count elements with a specific key. Searches the container for elements with a key equivalent to k and returns the number of matches.
                 *  Because all elements in a map container are unique, the function can only return 1 (if the element is found) or zero (otherwise).
                 */
                if (varToFreqCount.find(*itr4) != varToFreqCount.end()) {
                    varToFreqCount[*itr4]++;
                } else {
                    varToFreqCount[*itr4] = 1;
                }
            }
        }

        //STAGE2.2: now reverse the mapping from freq to variables
        unordered_map<int, int>::iterator itr5;
        map<int, list<int>, greater<int> > occurenceFreToVarMap; //descending order storage
        for (itr5 = varToFreqCount.begin(); itr5 != varToFreqCount.end(); itr5++) {
            occurenceFreToVarMap[itr5->second].push_back(itr5->first);
        }

        //STAGE3: start picking up variable (with max occurrence in min size clause) which has both polarity
        map<int, list<int>>::iterator itr6;
        for (itr6 = occurenceFreToVarMap.begin(); itr6 != occurenceFreToVarMap.end(); itr6++) {
            list<int>& varsWithMaxOccur = itr6->second;
            if (isDebug) {
                list<int>::iterator ditr1;
                cout << "<MOMS> Vars impacting maximally " << (itr6->first) << " clauses of minimum size:";
                for (ditr1 = varsWithMaxOccur.begin(); ditr1 != varsWithMaxOccur.end(); ditr1++) {
                    cout << *ditr1 << ',';
                }
                cout << endl << std::flush;
            }

            list<int>::iterator itr7;

            for (itr7 = varsWithMaxOccur.begin(); itr7 != varsWithMaxOccur.end(); itr7++) {
                //Following condition will ensure we pickup such variable which has both polarity.
                //Although this condition should not arise as call of removeSingularPolarityVars() will
                //ensure we get only bi-polar variables here
                if ((umap.find(*itr7) != umap.end()) && (umap.find((*itr7) * -1) != umap.end())) {
                    //TODO: tie break

                    //When isDirectionChoicePrioritizedAccordingToUnitClauseProp is set, intention is to trigger as much as possible reduction of clauses (not removal of clause)
                    return (isDirectionChoicePrioritizedAccordingToUnitClauseProp ? ((*itr7) * -1) : *itr7);
                }
            }

        }

    }

    assert(false);
    return (0);
}

int CDCLAlgo::biPolarityHeuristic(bool isDebug) const {
    typedef struct polarityStat {
        int positiveCount;
        int negativeCount;
        int var;
    } polarityStat;
    unordered_map<int, unordered_set<int>>::iterator itr1;
    map<unsigned int, list<polarityStat>, greater<int>> occurenceFreToVarMap; //descending order storage
    for (itr1 = umap.begin(); itr1 != umap.end(); itr1++) {
        if (((itr1->first > 0) && (itr1->second).size() > 0)) {

            if (umap.find((itr1->first) * (-1)) != umap.end()) {
                polarityStat ps;
                ps.positiveCount = (itr1->second).size();
                ps.negativeCount = umap[(itr1->first) * (-1)].size();
                ps.var = itr1->first;
                unsigned int reverse_polarity_occur = 0;
                switch (typeOfBiPolarHeuristic) {
                case SUM:
                    reverse_polarity_occur = umap[(itr1->first) * (-1)].size() + (itr1->second).size();
                    break;
                case DIFF:
                    reverse_polarity_occur = abs((int) (umap[(itr1->first) * (-1)].size() - (itr1->second).size()));
                    break;
                case PRODUCT:
                    reverse_polarity_occur = umap[(itr1->first) * (-1)].size() * (itr1->second).size();
                    break;
                case MAX:
                    reverse_polarity_occur = max(umap[(itr1->first) * (-1)].size(), (itr1->second).size());
                    break;
                default:
                    assert(false);
                }

                occurenceFreToVarMap[reverse_polarity_occur].push_back(ps);
            }
        }
    }

    list<polarityStat>& varsWithMaxOccur = occurenceFreToVarMap.begin()->second; //now get vars with max product for polarity counts
    if (isDebug) {
        list<polarityStat>::iterator ditr1;
        cout << "<MPP> Vars with max product-polarity-value of " << occurenceFreToVarMap.begin()->first << ':';
        for (ditr1 = varsWithMaxOccur.begin(); ditr1 != varsWithMaxOccur.end(); ditr1++) {
            cout << "<V" << (*ditr1).var << ':' << (*ditr1).negativeCount << "(-ve)," << (*ditr1).positiveCount
                    << "(+ve)> ";
        }
        cout << endl << std::flush;
    }

    if (isDirectionChoicePrioritizedAccordingToUnitClauseProp) {
        int candidateVar =
                (varsWithMaxOccur.front().positiveCount > varsWithMaxOccur.front().negativeCount) ?
                        (varsWithMaxOccur.front().var * -1) : varsWithMaxOccur.front().var; //intention is to trigger as much as possible reduction of clauses (not removal of clause)
        return (candidateVar);
    } else {
        int candidateVar =
                (varsWithMaxOccur.front().positiveCount > varsWithMaxOccur.front().negativeCount) ?
                        varsWithMaxOccur.front().var : (varsWithMaxOccur.front().var * -1); //intention is to trigger as much as removal of clauses (not reduction of clauses)
        return (candidateVar);
    }

    //TODO tie break;
    /*if (varsWithMaxOccur.size() > 0) {
     }*/
}

bool CDCLAlgo::removeSingularPolarityVars(bool isDebug) {

    int loopCount = 0;

    while (true) {

        unordered_map<int, unordered_set<int>>::iterator itr;
        unordered_set<int> clausesToBeDeleted;

        //Need to  be done in two passes as umap cannot be accessed for clause deletion when iteration is happening on it
        //to capture the affected clauses for singular polarity variable
        bool isAtleastOneSinglePolarityVarFound = false;
        for (itr = umap.begin(); itr != umap.end(); itr++) {
            if (umap.find(itr->first * -1) == umap.end()) { //single polarity variable

                if (isDebug) {
                    cout << "<Loop=" << loopCount << '>' << "Single polarity var = " << itr->first << endl
                            << std::flush;
                }
                isAtleastOneSinglePolarityVarFound = true;
                satResult.push_back(itr->first);

                unordered_set<int>& listOfAffectedClauses = umap[itr->first];
                unordered_set<int>::iterator iteratorForAffectedClauseIds;
                for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
                        iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
                    clausesToBeDeleted.insert(*iteratorForAffectedClauseIds); //will ensure unique clause-ids are inserted
                }
            }
        }

        if (!isAtleastOneSinglePolarityVarFound) {
            break;
        }

        if (isDebug) {
            unordered_set<int>::iterator iteratorForAffectedClauseIds;
            cout << "clauses to be deleted for single polarity reduction: ";
            for (iteratorForAffectedClauseIds = clausesToBeDeleted.begin();
                    iteratorForAffectedClauseIds != clausesToBeDeleted.end(); iteratorForAffectedClauseIds++) {
                cout << *iteratorForAffectedClauseIds << ',';
            }
            cout << endl << std::flush;
        }

        unordered_set<int>::iterator iteratorForAffectedClauseIds;
        for (iteratorForAffectedClauseIds = clausesToBeDeleted.begin();
                iteratorForAffectedClauseIds != clausesToBeDeleted.end(); iteratorForAffectedClauseIds++) {
            deleteClause(*iteratorForAffectedClauseIds);
        }

        loopCount++;
    }

    return ((loopCount > 0) ? true : false);
}

void CDCLAlgo::learnConflictReason(int conflictedVar, int originatingClauseID1, int originatingClauseID2, bool isDebug) {

    if(!clauseLearning){
        return;
    }

    if (isDebug) {
        unordered_map<int, VarAssignInfo>::iterator it;
        cout << "participatingVars1: [ClauseID=" << originatingClauseID1 << " coming from conflict literal " << (conflictedVar * -1) << "]";
        unordered_map<int, VarAssignInfo>& ancedentInfo1 = literalAncedentHistory[originatingClauseID1];
        for (it = ancedentInfo1.begin(); it != ancedentInfo1.end(); it++) {
            cout << it->first << "(L=" << (it->second).level << ", AC=" << (it->second).antecendentClause << ") ";
        }
        cout << endl << std::flush;
        cout << "participatingVars2: [ClauseID=" << originatingClauseID2 << " coming from conflict literal " << conflictedVar << "]";
        unordered_map<int, VarAssignInfo>& ancedentInfo2 = literalAncedentHistory[originatingClauseID2];
        for (it = ancedentInfo2.begin(); it != ancedentInfo2.end(); it++) {
            cout << it->first << "(L=" << (it->second).level << ", AC=" << (it->second).antecendentClause << ") ";
        }
        cout << endl << std::flush;
    }

    Clause learnedClause;

    if(!retractToHighestLevel){
        nonChronoBacktrackLevel = INT_MAX;

        unordered_map<int, VarAssignInfo>::iterator it;
        unordered_map<int, VarAssignInfo>& ancedentInfo1 = literalAncedentHistory[originatingClauseID1];
        for (it = ancedentInfo1.begin(); it != ancedentInfo1.end(); it++) {
            if(((it->first) != conflictedVar) && ((it->first) != (conflictedVar * -1))){
                int my_level = (it->second).level;
                if(my_level < nonChronoBacktrackLevel){
                    nonChronoBacktrackLevel = my_level;
                }
                //learnedClause.insertVar(freeVarAssignHist[my_level-1]*-1);
                learnedClause.insertVar(it->first);
            }
        }

        unordered_map<int, VarAssignInfo>& ancedentInfo2 = literalAncedentHistory[originatingClauseID2];
        for (it = ancedentInfo2.begin(); it != ancedentInfo2.end(); it++) {
            if(((it->first) != conflictedVar) && ((it->first) != (conflictedVar * -1))){
                int my_level = (it->second).level;
                if(my_level < nonChronoBacktrackLevel){
                    nonChronoBacktrackLevel = my_level;
                }
                //learnedClause.insertVar(freeVarAssignHist[my_level-1]*-1);
                learnedClause.insertVar(it->first);
            }
        }

    }else {

        nonChronoBacktrackLevel = -1;

        unordered_map<int, VarAssignInfo>::iterator it;
        unordered_map<int, VarAssignInfo>& ancedentInfo1 = literalAncedentHistory[originatingClauseID1];
        for (it = ancedentInfo1.begin(); it != ancedentInfo1.end(); it++) {
            if(((it->first) != conflictedVar) && ((it->first) != (conflictedVar * -1))){
                int my_level = (it->second).level;
                if(my_level > nonChronoBacktrackLevel){
                    nonChronoBacktrackLevel = my_level;
                }
                //learnedClause.insertVar(freeVarAssignHist[my_level-1]*-1);
                learnedClause.insertVar(it->first);
            }
        }

        unordered_map<int, VarAssignInfo>& ancedentInfo2 = literalAncedentHistory[originatingClauseID2];
        for (it = ancedentInfo2.begin(); it != ancedentInfo2.end(); it++) {
            if(((it->first) != conflictedVar) && ((it->first) != (conflictedVar * -1))){
                int my_level = (it->second).level;
                if(my_level > nonChronoBacktrackLevel){
                    nonChronoBacktrackLevel = my_level;
                }
                //learnedClause.insertVar(freeVarAssignHist[my_level-1]*-1);
                learnedClause.insertVar(it->first);
            }
        }
    }

    nonChronoBacktrackLevel --;
    assert(nonChronoBacktrackLevel != INT_MAX); //TODO should be lesser than max variable present in original clause
    learnedClause.setUniqueID(currentLearntClauseId);

    if (isDebug) {
        cout << "lowest-depth = " << nonChronoBacktrackLevel << " learned-clause [ID:" << learnedClause.getUniqueID() << "] = ";
        list<int>::iterator itLearnedClause;
        list<int> vars;
        learnedClause.fillWithVars(vars);
        for (itLearnedClause = vars.begin(); itLearnedClause != vars.end(); itLearnedClause++) {
            cout << *itLearnedClause << " ";
        }
        cout << endl << std::flush;
    }

    assert(!learnedClause.isEmptyClause());
    originalClauseStorage[currentLearntClauseId] = learnedClause;
    lastLearnedClauseFromChild = currentLearntClauseId;
    currentLearntClauseId ++;
}

bool CDCLAlgo::unitPropagate(bool isDebug, int level) {
    assert(0 == conflictDetectorForUnitClause.size());
    if (unitClause.size() > 0) {
        unordered_map<int, int>::iterator entryUnitClauseIt;
        for (entryUnitClauseIt = unitClause.begin(); entryUnitClauseIt != unitClause.end(); entryUnitClauseIt++) {
            //Ensure any unit clause handled is retained as history in conflictDetectorForUnitClause
            //This can be understood better by following example [2 -1][2 1] clauses where suppose in previous level split happened using -2
            //Thus current level will encounter [-1] and [1] as two unit clauses in 'unitClause' list. But if we don't retain
            //conflictDetectorForUnitClause[1] entry in history (even though 1 is handled as part of unit clause),
            //-1 will not be able to find out conflict as conflictDetectorForUnitClause[1] is not retained

            conflictDetectorForUnitClause[entryUnitClauseIt->first] = entryUnitClauseIt->second; //usage of set for unitClause will gurantee non-duplicated entry,
            //additionally conflictDetectorForUnitClause itself is set

            if (conflictDetectorForUnitClause.find((entryUnitClauseIt->first) * -1)
                    != conflictDetectorForUnitClause.end()) {
                if (isDebug) {
                    cout << "conflict detected through unit clause for " << (entryUnitClauseIt->first) << endl << std::flush;
                }
                learnConflictReason(entryUnitClauseIt->first,
                        conflictDetectorForUnitClause[(entryUnitClauseIt->first) * -1],
                        entryUnitClauseIt->second, isDebug);
                return (false); //conflict
            }
        }
    }

    //now unit propagate
    while (unitClause.size() > 0) {

        if (isDebug) {
            printCurrentUnitClauseQueue(unitClause);
            cout << endl << std::flush;
        }

        int unitVar = (unitClause.begin())->first;
        int originatingClauseID = (unitClause.begin())->second;
        unitClause.erase(unitVar);

        int complementUnitVar = unitVar * -1;
        satResult.push_back(unitVar);

        //The first check with respect to umap.find is very important , without that unnecessary blank element with complementUnitVar will be inserted in umap
        //It is important to note that we can landup into following scenarios where below mentioned checks are necessary
        //e.g. (x1+x2)*(x3*x2) suppose unit reduction queue started with !x1->!x3, !x1 will trigger a new unitVar = x2.
        //!x3 will ensure x2 as another unit var, but it will also remove reference to any clauseid corresponding to x2
        //Now finally when x2 is picked for unit var, it is not supposed to see any reference of x2 in umap.
        if (umap.find(unitVar) != umap.end()) {
            //Caution: do not use reference for listOfAffectedClauses. If we do so, we may land up in deleting from the same list
            //within deleteClause() which is being accessed (by reference) for iteration of affected clause
            unordered_set<int> listOfAffectedClauses = umap[unitVar]; //!!! CAUTION: if unitVar is not present, umap[unitVar] will insert that key
            unordered_set<int>::iterator iteratorForAffectedClauseIds;
            for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
                    iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
                deleteClause(*iteratorForAffectedClauseIds);
            }
        }

        if (umap.find(complementUnitVar) != umap.end()) {
            //Caution: do not use reference for listOfAffectedClauses. If we do so, we may land up in deleting from the same list
            //within deleteClause() which is being accessed (by reference) for iteration of affected clause
            unordered_set<int> listOfAffectedClauses = umap[complementUnitVar]; //!!! CAUTION: if complementUnitVar is not present, umap[complementUnitVar] will insert that key
            unordered_set<int>::iterator iteratorForAffectedClauseIds;
            for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
                    iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
                Clause& affectedClause = deleteVarFromClause(complementUnitVar, *iteratorForAffectedClauseIds, level, originatingClauseID);

                if (affectedClause.isSingleVariableClause()) { //after deletion of var, the clause has now become unit-var
                    int remainingVar = affectedClause.getUnitVar();

                    //Following condition check is replacement of checking empty clause check in original DPLL algo
                    //This can be understood by one small example - let us consider clause (1 + 2 + 3)
                    //Now suppose there is subsequent unit prop of !1, !2 and !3 which would have triggered empty clause.
                    //But in our implementation, as soon as the clause is remaining with last element, i.e. 3, it is moved to
                    //unitClause list. Thus, empty clause condition can be checked indirectly by checking presence of unit-compliment

                    if (conflictDetectorForUnitClause.find(remainingVar * -1) != conflictDetectorForUnitClause.end()) {
                        if (isDebug) {
                            cout << "conflict detected through unit clause for " << remainingVar << endl << std::flush;
                        }
                        learnConflictReason(remainingVar,
                                conflictDetectorForUnitClause[remainingVar * -1],
                                affectedClause.getUniqueID(), isDebug);
                        return (false);
                    }

                    unitClause[remainingVar] = affectedClause.getUniqueID(); //TODO: handling of duplicated unit-clause
                    conflictDetectorForUnitClause[remainingVar] = affectedClause.getUniqueID();
                    deleteClause(*iteratorForAffectedClauseIds);
                }
            }
        }
    }

    return (true);
}

void CDCLAlgo::addLearnedClauseFromChild(bool isDebug, int recusrsionDepth){
    if(!clauseLearning){
        return;
    }

    cdclLearnCount ++;
    if(cdclLearnCount > 1){ //retracting back to same level and same CDCLAlgo object - high chance it is UNSAT (let us fall back to DPLL)
        clauseLearning = false;
        if(isDebug){
            cout << "Clause learning is going to be stopped as retracting back to same level and object" << endl << std::flush;
        }
        return;
    }

    //TODO assignedLiterals check is not needed if learned clause is only from child
    unordered_set<int> assignedLiterals;
    map<int,int>::iterator it;
    for(it=freeVarAssignHist.begin(); it != freeVarAssignHist.end(); it ++){
        if(0 == it->second){
            continue;
        }
        if(isDebug){
            cout<< "(L=" << it->first << "," << it->second << ") ";
        }
        assignedLiterals.insert(it->second);
    }

    if(isDebug){
        cout << " lastLearnedClauseFromChild = " << lastLearnedClauseFromChild << endl << std::flush;
    }

    addClause(isDebug, originalClauseStorage[lastLearnedClauseFromChild], assignedLiterals);//TODO Audit whether same clause is being learned again and again

    /*for(int i=startIndexOfLearnedClause; i<= currentLearntClauseId; i++){
        if(originalClauseStorage.find(i) != originalClauseStorage.end()){
            if(clauseDB.find(i) == clauseDB.end()){
                if (isDebug) {
                    cout << "[Depth = " << recusrsionDepth << "] learned clause-id " << i << " will be added" << endl;
                }
                addClause(isDebug, originalClauseStorage[i], assignedLiterals);//TODO Audit whether same clause is being learned again and again
            }else{
                if (isDebug) {
                    cout << "[Depth = " << recusrsionDepth << "] learned clause-id " << i << " already present" << endl;
                }
            }
        }
    }*/

    if (isDebug) {
        cout << "Learned clause being added : " << endl << std::flush;
        printDebugInfo(recusrsionDepth, clauseDB, unitClause);
        printVarToClauseMapping(umap);
    }
}

bool CDCLAlgo::split(int var, bool isDebug, int recursionDepth) {

    int parentDepth = (recursionDepth - 1);
    if (isDebug) {
        cout << "[Depth=" <<  parentDepth << "]Splited on = " << var << endl << std::flush;
    }

    freeVarAssignHist[parentDepth] = var;

    //first clone umap, clauseDB and unitClause
    unordered_map<int, Clause> my_clauseDB = clauseDB;
    unordered_map<int, unordered_set<int>> my_umap = umap;
    unordered_map<int, int> my_unitClause = unitClause; //as part of singlepolar variable reduction, unitClause may be generated

    CDCLAlgo algoForNextRecursion(algo, typeOfBiPolarHeuristic,
            isDirectionChoicePrioritizedAccordingToUnitClauseProp, clauseLearning, retractToHighestLevel,
            my_clauseDB, my_umap, my_unitClause);
    algoForNextRecursion.literalAncedentHistory = literalAncedentHistory;
    algoForNextRecursion.freeVarAssignHist = freeVarAssignHist;
    algoForNextRecursion.setVariableToTrue(var, isDebug, parentDepth);

    if (true == algoForNextRecursion.runCDCLAlgo(isDebug, recursionDepth)) {
        satResult.push_back(var);
        list<int>& res = algoForNextRecursion.getSatResult();
        list<int>::iterator resIt;
        for (resIt = res.begin(); resIt != res.end(); resIt++) {
            satResult.push_back(*resIt);
        }
        freeVarAssignHist[parentDepth] = 0; //reset
        return (true);
    }

    nonChronoBacktrackLevel = algoForNextRecursion.nonChronoBacktrackLevel;
    lastLearnedClauseFromChild = algoForNextRecursion.lastLearnedClauseFromChild;
    freeVarAssignHist[parentDepth] = 0; //reset
    return (false);
}

bool CDCLAlgo::runCDCLAlgo(bool isDebug, int recursionDepth) {

    if (isDebug) {
        cout << "[Depth=" << recursionDepth << "]Initially - Clause count = " << clauseDB.size() << " variable count = "
                << umap.size() << endl;
        printDebugInfo(recursionDepth, clauseDB, unitClause);
        printVarToClauseMapping(umap);
    }

    if(0 == recursionDepth){
        assert(originalClauseStorage.empty());
        assert(-1 == currentLearntClauseId);
        assert(-1 == startIndexOfLearnedClause);
        originalClauseStorage = clauseDB; //keeping original reference
        currentLearntClauseId = originalClauseStorage.size();
        startIndexOfLearnedClause = currentLearntClauseId;
    }

restart:

    nonChronoBacktrackLevel = -1;
    lastLearnedClauseFromChild = -1;
    conflictDetectorForUnitClause.clear();//Due to CDCL's restart we may get non-zero size conflictDetectorForUnitClause at this point -so we need to clear

    int originalUnitClauseSize = unitClause.size();
    if(!unitPropagate(isDebug, recursionDepth)){
        return (false);
    }

    if (clauseDB.empty() && unitClause.empty()) {
        return (true); //SAT
    }

    if (isDebug && (originalUnitClauseSize > 0)) {
        cout << "After unit clause reduction - Clause count = " << clauseDB.size() << " variable count = "
                << umap.size() << endl;
        printDebugInfo(recursionDepth, clauseDB, unitClause);
        printVarToClauseMapping(umap);
    }

    bool singlePolarReduction = removeSingularPolarityVars(isDebug);
    if (isDebug && singlePolarReduction) {
        cout << "After single Polar reduction - Clause count = " << clauseDB.size() << " variable count = "
                << umap.size() << endl;
        printDebugInfo(recursionDepth, clauseDB, unitClause);
        printVarToClauseMapping(umap);
    }

    if (clauseDB.empty()) {
        if (!unitClause.empty()) {
            if (isDebug) {
                cout << "Re-triggering unit clause reduction" << endl << std::flush;
            }
            return (unitPropagate(isDebug, recursionDepth));
        }
        return (true); //SAT
    }

    int splitVar = chooseSplitVarAccordingtoHeuristic(isDebug);
    assert(splitVar != 0);

    if (split(splitVar, isDebug, recursionDepth + 1)) {
        return (true);
    }else{
        if(clauseLearning){
            if(nonChronoBacktrackLevel != -1){

                if(nonChronoBacktrackLevel != recursionDepth){
                    return (false); //non-chrono back-tracking
                }else {
                    if(isDebug){
                        cout << "[Depth " << recursionDepth << "] back tracked to level through stage1 recursion" << endl << std::flush;
                    }
                    addLearnedClauseFromChild(isDebug, recursionDepth);
                    goto restart;
                }
            }else{
                if(isDebug){
                    cout << "[Depth " << recursionDepth << "] falling down to other stage of split-var = " << splitVar << endl << std::flush;
                }
            }
        }
    }

    if (split(splitVar * -1, isDebug, recursionDepth + 1)) {
        return (true);
    } else{
        if(clauseLearning){
            if(nonChronoBacktrackLevel != -1){
                if(nonChronoBacktrackLevel != recursionDepth){
                    return (false); //non-chrono back-tracking
                }else{
                    if(isDebug){
                        cout << "[Depth " << recursionDepth << "] back tracked to level through stage2 recursion" << endl << std::flush;
                    }
                    addLearnedClauseFromChild(isDebug, recursionDepth);
                    goto restart;
                }
            }
        }
    }

    if(isDebug){
        cout << "[Depth " << recursionDepth << "] both side assignment failed for " << splitVar << endl << std::flush;
    }

    return (false);
}

//================== DimacsParser.h ======================
class DimacsParser {
private:
    int maxVarCount;
    int maxClauseCount;
    int currentParsedClauseIndex;
    unordered_map<int, unordered_set<int>> umap; //map of variable to list of clause-id (each clause is assigned unique id)
    unordered_map<int, Clause> clauseDB; //map of unique clause-id to actual clauses
    unordered_map<int, int> unitClause; //if any
    void parseMetaHeaderLine(const char* line);
    void parseClauseLine(const char* line);

public:
    DimacsParser();
    virtual ~DimacsParser();
    void parse(FILE* in, bool isDebug);
    int getMaxVarCount() const {
        return (maxVarCount);
    }
    int getMaxClauseCount() const {
        return (maxClauseCount);
    }
    unordered_map<int, Clause>& getClauses() {
        return (clauseDB);
    }
    unordered_map<int, unordered_set<int>>& getVarToClauseMapping() {
        return (umap);
    }
    unordered_map<int, int>& getListOfUnitClausesIfAny() {
        return (unitClause);
    }
};

// ======================= DimacsParser.cpp ================
DimacsParser::DimacsParser() :
                maxVarCount(0), maxClauseCount(0), currentParsedClauseIndex(0) {
}

DimacsParser::~DimacsParser() {
}

void DimacsParser::parseMetaHeaderLine(const char* line) {
    int lineLen = strlen(line);
    char bufPerToken[256];
    int posInTokenBuf = 0;
    bool tokenParsingState = false;
    int values[2];
    int currentParsedToken = 0;
    for (int i = 1; i < lineLen; i++) { //first char is known to be 'p' - thus starting with index 1
        if (('0' <= line[i]) && (line[i] <= '9')) {
            bufPerToken[posInTokenBuf] = line[i];
            posInTokenBuf++;
            tokenParsingState = true;
        } else {
            if (tokenParsingState) {
                if (currentParsedToken >= 2) {
                    throw std::logic_error("");
                }
                bufPerToken[posInTokenBuf] = '\0';
                values[currentParsedToken] = atoi(bufPerToken);
                currentParsedToken++;
            }
            tokenParsingState = false;
            posInTokenBuf = 0;
        }
    }

    maxVarCount = values[0];
    maxClauseCount = values[1];
}

void DimacsParser::parseClauseLine(const char* line) {

    if (currentParsedClauseIndex >= maxClauseCount) {
        throw std::logic_error("");
    }

    int lineLen = strlen(line);
    char bufPerToken[256];
    int posInTokenBuf = 0;
    bool tokenParsingState = false;
    Clause c;
    for (int i = 0; i < lineLen; i++) {
        if ((line[i] != '+') && (line[i] != '-') && ((line[i] < '0') || ('9' < line[i]))) {
            if (tokenParsingState) {
                bufPerToken[posInTokenBuf] = '\0';
                int token = atoi(bufPerToken);
                if (0 == token) { //terminating zero found
                    break;
                }
                c.insertVar(token);
            }
            tokenParsingState = false;
            posInTokenBuf = 0;
        } else {
            bufPerToken[posInTokenBuf] = line[i];
            posInTokenBuf++;
            tokenParsingState = true;
        }
    }

    if (c.isEmptyClause()) {

    } else if (c.isSingleVariableClause()) {
        unitClause[c.getUnitVar()] = -1; //-1 as clauseid where unit-clause was originated, indicates this unit-clauses were present directly as part of original input
    } else {

        c.setUniqueID(currentParsedClauseIndex);
        clauseDB[currentParsedClauseIndex] = c;

        list<int> listOfVars;
        c.fillWithVars(listOfVars);
        list<int>::iterator it;
        for (it = listOfVars.begin(); it != listOfVars.end(); it++) {
            umap[*it].insert(currentParsedClauseIndex);
        }
    }
    currentParsedClauseIndex++;
}

//FILE* is used for performance purpose - although it is c-styled
void DimacsParser::parse(FILE* in, bool isDebug) {
    char* line = NULL;
    size_t len = 0;
    int charRead = 0;

    assert(in != NULL);

    /*
     * getline() reads an entire line from stream, storing the address of
     the buffer containing the text into *lineptr.  The buffer is null-
     terminated and includes the newline character, if one was found.

     If *lineptr is set to NULL and *n is set 0 before the call, then
     getline() will allocate a buffer for storing the line.  This buffer
     should be freed by the user program even if getline() failed.

     Alternatively, before calling getline(), *lineptr can contain a
     pointer to a malloc(3)-allocated buffer *n bytes in size.  If the
     buffer is not large enough to hold the line, getline() resizes it
     with realloc(3), updating *lineptr and *n as necessary.
     */
    while ((charRead = getline(&line, &len, in)) != -1) {
        if (isDebug) {
            cout << "[ClauseID:" << currentParsedClauseIndex << "]" << line << std::flush;
        }

        //trimming from beginning blank spaces
        int firstCharEffectiveStartIndex = 0;
        while ((' ' == line[firstCharEffectiveStartIndex]) || ('\t' == line[firstCharEffectiveStartIndex])) {
            firstCharEffectiveStartIndex++;
        }

        char firstChar = line[firstCharEffectiveStartIndex];
        if ((firstChar != '+') && (firstChar != '-') && (firstChar != 'p')
                && ((firstChar < '1') || ('9' < firstChar))) {
            continue; //ignorable line encountered e.g. comment line or line starting with % or line with single zero
        }

        if ('p' == firstChar) {
            if ((maxVarCount > 0) || (maxClauseCount > 0)) {
                throw std::logic_error(""); //only single line with 'p' allowed
            }
            parseMetaHeaderLine(line);
            continue;
        }

        parseClauseLine(&line[firstCharEffectiveStartIndex]);

        if (currentParsedClauseIndex >= maxClauseCount) {
            if (isDebug) {
                cout << "Breaking from parsing" << endl << std::flush;
            }
            break;
        }
    }

    free(line);
}

// ======================== DirectoryListing ===========

class DirectoryListing {
private:
    list<string> listOfFileName;
public:
    bool openDir(char* dirPath) {
        DIR *dir;
        struct dirent *ent;
        if ((dir = opendir(dirPath)) != NULL) {
            /* print all the files and directories within directory */
            while ((ent = readdir(dir)) != NULL) {
                string fileName(dirPath);
                fileName.append("\\");
                listOfFileName.push_back(fileName.append(ent->d_name));
            }
            closedir(dir);
            return (true);
        } else {
            return (false);
        }
    }

    void getFileNames(list<string>& filenames) {
        filenames = listOfFileName; //copying
    }
};

// ============================ MAIN ====================

bool validateSATResult(int* finalFormattedResult, int maxVarCount, unordered_map<int, Clause> originalClauses) {
    unordered_map<int, Clause>::iterator it;
    for (it = originalClauses.begin(); it != originalClauses.end(); it++) {
        list<int> listOfVars;
        (it->second).fillWithVars(listOfVars);
        bool atleastOneVarTrue = false;
        while (!listOfVars.empty()) {
            int var = listOfVars.front();
            assert(var != 0);
            if (var > 0) {
                if (finalFormattedResult[var] == var) {
                    atleastOneVarTrue = true;
                    break;
                }
            } else {
                if (finalFormattedResult[var * -1] == var) {
                    atleastOneVarTrue = true;
                    break;
                }
            }
            listOfVars.pop_front();
        }
        if (!atleastOneVarTrue) {
            cout << endl << "====> [C" << it->first << ':';
            list<int> vars;
            (it->second).fillWithVars(vars);
            list<int>::iterator varsInClause;
            for (varsInClause = vars.begin(); varsInClause != vars.end(); varsInClause++) {
                cout << *varsInClause << ',';
            }
            cout << ']' << endl;
            return (false);
        }
    }
    return (true);
}

void runAlgoForComparativeStudy(HeuristicAlgo algo, BiPolarityHeuristic bipolarHeuristic,
        bool isDirectionChoicePrioritiedAccordingToUnitClauseProp, bool isClauseLearning, bool retractToHighest, const char* alogID, ofstream& timingOut,
        ofstream& resultOut, DimacsParser& dimParser) {

    int maxVarCount = dimParser.getMaxVarCount();

    //As original inputs will mutated within runDPLLAlgo(), will be cloning the original content from dimParser
    unordered_map<int, Clause> originalClauses = dimParser.getClauses();
    unordered_map<int, unordered_set<int>> originalVarToClauseMapping = dimParser.getVarToClauseMapping();
    unordered_map<int, int> originalUnitClauses = dimParser.getListOfUnitClausesIfAny();

    long long microseconds = -1;
    auto start = std::chrono::high_resolution_clock::now();

    CDCLAlgo dpLLAlgo(algo, bipolarHeuristic,
            isDirectionChoicePrioritiedAccordingToUnitClauseProp, isClauseLearning,retractToHighest,
            originalClauses, originalVarToClauseMapping, originalUnitClauses);

    resultOut << alogID << " ";
    if (dpLLAlgo.runCDCLAlgo(false, 0)) {

        auto elapsed = std::chrono::high_resolution_clock::now() - start;
        microseconds = std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count();
        resultOut << "SAT" << " ";
        int* finalFormattedResult = new int[maxVarCount + 1];
        memset(finalFormattedResult, 0, (maxVarCount + 1) * sizeof(int));
        list<int>& result = dpLLAlgo.getSatResult();
        list<int>::iterator varsInResult;
        for (varsInResult = result.begin(); varsInResult != result.end(); varsInResult++) {
            if (*varsInResult > 0) {
                finalFormattedResult[*varsInResult] = *varsInResult;
            } else {
                finalFormattedResult[(*varsInResult) * -1] = *varsInResult;
            }
        }
        for (int i = 1; i <= maxVarCount; i++) {
            if (finalFormattedResult[i] != 0) {
                resultOut << finalFormattedResult[i] << " ";
            } else {
                finalFormattedResult[i] = i;
                resultOut << '[' << i << "] ";
            }
        }
        resultOut << "0\n";
        assert(validateSATResult(finalFormattedResult, maxVarCount, dimParser.getClauses()));

        delete[] finalFormattedResult;

    } else {

        auto elapsed = std::chrono::high_resolution_clock::now() - start;
        microseconds = std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count();
        resultOut << "UNSAT\n";
    }

    resultOut.flush();
    timingOut << microseconds << ',';
    timingOut.flush();

    CDCLAlgo::resetCDCL();
}

void comparativeStudyOfHeuristics(FILE* in, ofstream& timingOut, ofstream& resultOut) {
    try {
        DimacsParser dimParser;
        dimParser.parse(in, false);
        runAlgoForComparativeStudy(MOMS, NONE, true, false, false, "MOMS-U", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(MOMS, NONE, false, false, false, "MOMS-R", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, SUM, true, false, false, "BIPOLAR-SUM-U", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, SUM, false, false, false, "BIPOLAR-SUM-R", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, DIFF, true, false, false, "BIPOLAR-DIFF-U", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, DIFF, false, false, false, "BIPOLAR-DIFF-R", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, PRODUCT, true, false, false, "BIPOLAR-PROD-U", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, PRODUCT, false, false, false, "BIPOLAR-PROD-R", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, MAX, true, false, false, "BIPOLAR-MAX-U", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, MAX, false, false, false, "BIPOLAR-MAX-R", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(MOMS, NONE, false, true, true, "MOMS-R-CDCL-H", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(MOMS, NONE, false, true, false, "MOMS-R-CDCL-L", timingOut, resultOut, dimParser);
        timingOut << "\n";
        return;
    } catch (exception& e) {
        cerr << e.what() << std::flush;
    } catch (...) {
        cerr << "\nException occur.";
    }
    assert(false);
}

void initiateAutoCompareAmongstAlgo(list<string>& files) {
    ofstream resultTime;
    resultTime.open("timing.csv");

    ofstream resultOut;
    resultOut.open("result_out.txt");

    list<string>::iterator it;
    int fileID = 0;
    for (it = files.begin(); it != files.end(); it++, fileID++) {
        resultTime << fileID << ',';
        resultOut << fileID << ' ' << *it << "\n";
        FILE* file = fopen((*it).c_str(), "r");
        comparativeStudyOfHeuristics(file, resultTime, resultOut);
        fclose(file);
    }

    resultTime.close();
    resultOut.close();
}

bool determineSATOrUNSAT(FILE* in, bool debug, bool isTimingToBePrinted, HeuristicAlgo algo,
        BiPolarityHeuristic biPolarHeuSubType, bool isDirectionPriorityInUnitClauseProp,
        bool crossValidateToBeDone, bool conflictDrivenLearning, bool retractToHighestLevel) {
    try {

        DimacsParser dimParser;
        dimParser.parse(in, debug);
        int maxVarCount = dimParser.getMaxVarCount();

        if (debug) {
            cout << "maxVarCount = " << maxVarCount << " maxClauseCount = " << dimParser.getMaxClauseCount() << endl;
        }

        if (BI_POLARITY_STAT == algo) {
            assert(biPolarHeuSubType != NONE);
        }

        //As original inputs will mutated within runDPLLAlgo(), will be cloning the original content from dimParser
        unordered_map<int, Clause> originalClauses = dimParser.getClauses();
        unordered_map<int, unordered_set<int>> originalVarToClauseMapping = dimParser.getVarToClauseMapping();
        unordered_map<int, int> originalUnitClauses = dimParser.getListOfUnitClausesIfAny();

        long long microseconds = -1;
        auto start = std::chrono::high_resolution_clock::now();

        CDCLAlgo dpLLAlgo(algo, biPolarHeuSubType, isDirectionPriorityInUnitClauseProp,conflictDrivenLearning, retractToHighestLevel,
                originalClauses, originalVarToClauseMapping, originalUnitClauses);


        if (dpLLAlgo.runCDCLAlgo(debug, 0)) {

            auto elapsed = std::chrono::high_resolution_clock::now() - start;
            microseconds = std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count();
            cout << "SAT" << endl;
            int* finalFormattedResult = new int[maxVarCount + 1];
            memset(finalFormattedResult, 0, (maxVarCount + 1) * sizeof(int));
            list<int>& result = dpLLAlgo.getSatResult();
            list<int>::iterator varsInResult;
            for (varsInResult = result.begin(); varsInResult != result.end(); varsInResult++) {
                if (*varsInResult > 0) {
                    finalFormattedResult[*varsInResult] = *varsInResult;
                } else {
                    finalFormattedResult[(*varsInResult) * -1] = *varsInResult;
                }
            }
            for (int i = 1; i <= maxVarCount; i++) {
                if (finalFormattedResult[i] != 0) {
                    cout << finalFormattedResult[i] << " ";
                } else {
                    finalFormattedResult[i] = i;
                    //cout << '[' << i << "] ";
                    cout << i << " ";
                }
            }
            cout << "0" << std::flush;
            if (crossValidateToBeDone) {
                assert(validateSATResult(finalFormattedResult, maxVarCount, dimParser.getClauses()));
            }
            delete[] finalFormattedResult;

        } else {

            auto elapsed = std::chrono::high_resolution_clock::now() - start;
            microseconds = std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count();
            cout << "UNSAT" << std::flush;
        }

        if (isTimingToBePrinted) {
            cout << endl << "Time elapsed (micro-sec) = " << microseconds << endl << std::flush;
        }

        CDCLAlgo::resetCDCL();

        return (true);
    } catch (exception& e) {
        cerr << e.what() << std::flush;
    } catch (...) {
        cerr << "\nException occur.";
    }

    return (false);
}

/*************************************************************
 * COMMAND LINE OPTIONS
 *
 * The program runs in three modes -
 * [1] Compare runtime between different choice of heuristics - in this mode,
 *     output will be generated in timing.csv and result_out.txt. timing.csv can be easily exported in excel
 *     for post-processing (plotting graphs etc.). In this mode, all the formula files under a particular
 *     directory will be read and solved one after another for each of the heuristic algo (presently, MOMS,
 *     BIPOLAR-SUM, BIPOLAR-DIFF, BIPOLAR-PROD and BIPOLAR-MAX). This mode is enabled using -a and providing
 *     directory information through -dir. In this mode, each SAT output is also automatically cross validated against
 *     original formula.
 *
 * [2.1] Solving formulas for all the files under a particular directory. It is enabled by providing directory information
 *       through -dir. Output in this mode is written to stdout.
 * [2.2] In absence of -dir, input formula is read directly from stdin.
 * In both 2.1 and 2.2, additionally following options can be enabled -
 * -d : enables debug log in stdout
 * -t : calculates timing in microsecond granularity (timing does not include parsing of DIMACS file - it shows only DPLL algo runtime)
 * -c : cross validates the SAT output by putting it in original formula.
 * -h : changes heuristic (e.g. MOMS, BI_POLARITY_STAT and MAX_UNIT_PROP_TRIGGER)
 *      if BI_POLARITY_STAT is enabled it expects additional options of SUM, DIFF, PRODUCT or MAX
 * -p : set direction heuristic such a way isDirectionChoicePrioritizedAccordingToUnitClauseProp set to true.
 * -l : disable conflict driven learning
 *
 * CAUTION: There is no validation check while command line argument parsing - you may face segmentation fault if you miss required arguments.
 *************************************************************/

int main(int argc, char *argv[]) {

    bool debug = false;
    bool isTimingToBePrinted = false;
    bool isDirectoryMode = false;

    char* dir = NULL;
    HeuristicAlgo algo = MOMS;
    BiPolarityHeuristic biPolarHeuSubType = NONE;
    bool crossValidateToBeDone = false;
    bool autoCompareMode = false;
    bool isDirectionPriorityInUnitClauseProp = false;
    bool conflictDrivenLearning = true;
    bool retractToHighestLevel = true;

    if (argc > 1) {
        for (int i = 1; i < argc; i++) {
            if (0 == strcmp("-d", argv[i])) {
                debug = true;
            } else if (0 == strcmp("-t", argv[i])) {
                isTimingToBePrinted = true;
            } else if (0 == strcmp("-a", argv[i])) {
                autoCompareMode = true;
            } else if (0 == strcmp("-p", argv[i])) {
                isDirectionPriorityInUnitClauseProp = true;
            } else if (0 == strcmp("-c", argv[i])) {
                crossValidateToBeDone = true;
            } else if (0 == strcmp("-l", argv[i])) {
                conflictDrivenLearning = false;
            } else if (0 == strcmp("-lo", argv[i])) {
                retractToHighestLevel = false;
            } else if (0 == strcmp("-dir", argv[i])) {
                isDirectoryMode = true;
                dir = argv[i + 1];
            } else if (0 == strcmp("-h", argv[i])) {
                char* heuristic = argv[i + 1];
                if (0 == strcmp("MOMS", heuristic)) {
                    algo = MOMS;
                } else if (0 == strcmp("BI_POLARITY_STAT", heuristic)) {
                    algo = BI_POLARITY_STAT;
                    char* type = argv[i + 2];
                    if (0 == strcmp("SUM", type)) {
                        biPolarHeuSubType = SUM;
                    } else if (0 == strcmp("DIFF", type)) {
                        biPolarHeuSubType = DIFF;
                    } else if (0 == strcmp("PRODUCT", type)) {
                        biPolarHeuSubType = PRODUCT;
                    } else if (0 == strcmp("MAX", type)) {
                        biPolarHeuSubType = MAX;
                    }
                } else {
                    cerr << "Invalid heuristic algo = " << heuristic;
                    return (1);
                }
            }
        }
    }

    if (isDirectoryMode) {
        DirectoryListing dirListing;
        if (!dirListing.openDir(dir)) {
            cerr << "directory listing failed for " << dir;
            return (1);
        }

        list<string> files;
        dirListing.getFileNames(files);

        if (autoCompareMode) {
            initiateAutoCompareAmongstAlgo(files);
            return (0);
        }

        list<string>::iterator it;
        for (it = files.begin(); it != files.end(); it++) {
            cout << *it << endl << std::flush;
            FILE* file = fopen((*it).c_str(), "r");
            determineSATOrUNSAT(file, debug, isTimingToBePrinted, algo, biPolarHeuSubType,
                    isDirectionPriorityInUnitClauseProp, crossValidateToBeDone, conflictDrivenLearning, retractToHighestLevel);
            fclose(file);
        }

    } else {
        if (!determineSATOrUNSAT(stdin, debug, isTimingToBePrinted, algo, biPolarHeuSubType,
                isDirectionPriorityInUnitClauseProp, crossValidateToBeDone, conflictDrivenLearning, retractToHighestLevel)) {
            cerr << "determineSATOrUNSAT failed from stdin";
            return (1);
        }
    }

    return (0);
}

