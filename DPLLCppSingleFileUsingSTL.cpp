//============================================================================
// Name        : DPLLCppSingleFileUsingSTL.cpp
// Author      : Shaswata Jash
// Version     :
// Description : Implementation of DPLL Algorithm with additional enhancement of lookAheadUnitPropagate, removeSingularPolarityVars
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
 *       return (true); //SAT
 *   }
 *
 *   if (split(splitVar * -1, isDebug, recursionDepth + 1)) {
 *       return (true); //SAT
 *   }
 *
 *   return (false); //UNSAT
 *}
 * In the above code flow, lookAheadUnitPropagate() and removeSingularPolarityVars() steps are actually outside of the original
 * steps mentioned in DPLL Algorithm. Additionally, you would be also observing another difference that we don't check explicitly
 * empty clause (a clause which has no literals) for UNSAT -as due to our choice of having unitClause in separate data-structure
 * than normal clauses, empty clause condition is translated as conflict detection in present implementation.
 *
 * By default lookAheadUnitPropagate() is switched off as it is helpful mainly for very hard problem to keep depth of search tree shallow,
 * in lieu of performance overhead of doing look ahead unit-clause propagate for each of the unassigned literals.
 ***************************************************************************************************************************/

/**********************************************************************************************************
 * Brief description of Heuristics Algo
 * There are mainly three heuristics algorithms -
 * MOMS: Maximum Occurrence of variable in Minimum size clauses [Refer:DPLLAlgo::momsHeuristic()]
 * BI_POLARITY_STAT: Heuristics based on count of both polarities of a particular variables (further choice of SUM, DIFF, PRODUCT and MAX)
 *                   [Refer : DPLLAlgo::biPolarityHeuristic()]
 * MAX_UNIT_PROP_TRIGGER: This heuristics internally expects lookAheadUnitPropagate() is enabled. It splits on variable according to
 *                        which will trigger maximum unit-clause propagation in next stage. [Refer: DPLLAlgo::maxUnitPropTriggerHeuristic()]
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
        return ((0 == literals.size()) ? true : false);
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
};

// ========================================== DPLLAlgo ========================

typedef enum HeuristicAlgo {
    MOMS, BI_POLARITY_STAT, MAX_UNIT_PROP_TRIGGER
} HeuristicAlgo;

typedef enum BiPolarityHeuristic {
    SUM, DIFF, PRODUCT, MAX, NONE
} BiPolarityHeuristic;

class DPLLAlgo {
private:

    HeuristicAlgo algo;
    BiPolarityHeuristic typeOfBiPolarHeuristic;

    //For all the below three reference variable, data in them will be changed (majorly deleted but for unitClause, elements
    // can be added too) - thus caller of runDPLLAlgo() should rely sanctity of these variables after return from the functions.
    unordered_map<int, Clause>& clauseDB; //map of unique clause-id to actual clauses
    unordered_map<int, unordered_set<int>>& umap; //map of variable to list of clause-id (each clause is assigned unique id)
    unordered_set<int>& unitClause; //due to usage of set, it will gurantee non-duplicate entry

    int unitClauseReductionCount;
    unordered_map<int, int> splitVarToUnitPropFreq;

    unordered_set<int> conflictDetectorForUnitClause;
    list<int> satResult;

    bool isLookAheadUnitPropStepEnabled;

    int momsHeuristic(bool isDebug) const;
    int biPolarityHeuristic(bool isDebug) const;
    int maxUnitPropTriggerHeuristic(bool isDebug);

    int chooseSplitVarAccordingtoHeuristic(bool isDebug) {

        switch (algo) {
        case MOMS:
            return (momsHeuristic(isDebug));
        case BI_POLARITY_STAT:
            return (biPolarityHeuristic(isDebug));
        case MAX_UNIT_PROP_TRIGGER:
            return (maxUnitPropTriggerHeuristic(isDebug));
        default:
            assert(false);
        }
        return (0);
    }

    static void deleteClause(int clauseSeqId, unordered_map<int, Clause>& my_clauseDB,
            unordered_map<int, unordered_set<int>>& my_umap) {

        if (my_clauseDB.find(clauseSeqId) == my_clauseDB.end()) {
            stringstream fmt;
            fmt << __FILE__ << ':' << __LINE__ << " No matching clauseid " << clauseSeqId << " found";
            throw logic_error(fmt.str());
        }
        Clause& affectedClause = my_clauseDB[clauseSeqId];

        list<int> vars;
        affectedClause.fillWithVars(vars);

        //remove reference of clauseid from affected variable
        list<int>::iterator iteratorForAffectedVars;
        list<int> deletableVarsFromUmap;
        for (iteratorForAffectedVars = vars.begin(); iteratorForAffectedVars != vars.end(); iteratorForAffectedVars++) {
            my_umap[*iteratorForAffectedVars].erase(clauseSeqId);
            if (0 == my_umap[*iteratorForAffectedVars].size()) {
                deletableVarsFromUmap.push_back(*iteratorForAffectedVars);
            }
        }
        for (iteratorForAffectedVars = deletableVarsFromUmap.begin();
                iteratorForAffectedVars != deletableVarsFromUmap.end(); iteratorForAffectedVars++) {
            if (my_umap.erase(*iteratorForAffectedVars) <= 0) {
                stringstream fmt;
                fmt << __FILE__ << ':' << __LINE__ << " variable= " << (*iteratorForAffectedVars)
                        << " cannot be erased from umap";
                throw std::logic_error(fmt.str());
            }
        }

        //now remove the clause-id itself
        my_clauseDB.erase(clauseSeqId);
    }

    static Clause& deleteVarFromClause(int var, int clauseSeqId, unordered_map<int, Clause>& my_clauseDB,
            unordered_map<int, unordered_set<int>>& my_umap) {
        Clause& affectedClause = my_clauseDB[clauseSeqId];
        affectedClause.deleteVar(var);
        my_umap[var].erase(clauseSeqId);
        if (0 == my_umap[var].size()) {
            if (my_umap.erase(var) <= 0) {
                stringstream fmt;
                fmt << __FILE__ << ':' << __LINE__ << " variable= " << (var) << " cannot be erased from umap";
                throw std::logic_error(fmt.str());
            }
        }
        return (affectedClause);
    }

    int getFormulaRelativeComplexityWeight() {
        unordered_map<int, Clause>::iterator it;
        int product = 1;
        for (it = clauseDB.begin(); it != clauseDB.end(); it++) {
            product *= (it->second).getVariablesListSize();
        }
        return (product);
    }

    static void printCurrentUnitClauseQueue(unordered_set<int>& unitClause);
    static void printDebugInfo(int recursionDepth, unordered_map<int, Clause>& clauseDB,
            unordered_set<int>& unitClause);
    static void printVarToClauseMapping(unordered_map<int, unordered_set<int>>& my_umap);
    static void setVariableToTrue(int var, bool isDebug, unordered_map<int, Clause>& my_clauseDB,
            unordered_map<int, unordered_set<int>>& my_umap, unordered_set<int>& my_unitClause);
    bool split(int var, bool isDebug, int recursionDepth);
    bool removeSingularPolarityVars(bool isDebug);
    bool unitPropagate(bool isDebug);
    bool lookAheadUnitPropagate(bool isDebug);

public:
    bool runDPLLAlgo(bool isDebug, int recursionDepth);

    list<int>& getSatResult() {
        return (satResult);
    }

    DPLLAlgo(HeuristicAlgo my_algo, BiPolarityHeuristic subType, bool lookAheadEnabled,
            unordered_map<int, Clause>& my_clauseDB, unordered_map<int, unordered_set<int>>& my_umap,
            unordered_set<int>& my_unitClause) :
            algo(my_algo), typeOfBiPolarHeuristic(subType), clauseDB(my_clauseDB), umap(my_umap), unitClause(
                    my_unitClause), unitClauseReductionCount(0), isLookAheadUnitPropStepEnabled(lookAheadEnabled) {
        if (MAX_UNIT_PROP_TRIGGER == my_algo) {
            isLookAheadUnitPropStepEnabled = true;
        }
    }
};

void DPLLAlgo::printCurrentUnitClauseQueue(unordered_set<int>& my_unitClause) {
    unordered_set<int>::iterator singleClauseIt;
    if (my_unitClause.size() > 0) {
        cout << "[S:";
        for (singleClauseIt = my_unitClause.begin(); singleClauseIt != my_unitClause.end(); singleClauseIt++) {
            cout << *singleClauseIt << ',';
        }
        cout << ']';
    }
}

void DPLLAlgo::printDebugInfo(int recursionDepth, unordered_map<int, Clause>& my_clauseDB,
        unordered_set<int>& my_unitClause) {
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

void DPLLAlgo::printVarToClauseMapping(unordered_map<int, unordered_set<int>>& my_umap) {
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

void DPLLAlgo::setVariableToTrue(int var, bool isDebug, unordered_map<int, Clause>& my_clauseDB,
        unordered_map<int, unordered_set<int>>& my_umap, unordered_set<int>& my_unitClause) {

    //The first check with respect to umap.find is very important , without that unnecessary blank element with complementUnitVar will be inserted in umap
    //It is important to note that we can landup into following scenarios where below mentioned checks are necessary
    //e.g. (x1+x2)*(x3*x2) suppose variable setting started (refer lookAheadUnitPropagate function) with !x1->!x3, !x1 will trigger a new unitVar = x2.
    //!x3 will ensure x2 as another unit var, but it will also remove reference to any clauseid corresponding to x2
    //Now finally when x2 is picked for unit var, it is not supposed to see any reference of x2 in umap

    if (my_umap.find(var) != my_umap.end()) {

        //Caution: do not use reference for listOfAffectedClauses. If we do so, we may land up in deleting from the same list
        //within deleteClause() which is being accessed (by reference) for iteration of affected clause
        unordered_set<int> listOfAffectedClauses = my_umap[var];
        unordered_set<int>::iterator iteratorForAffectedClauseIds;
        for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
                iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
            deleteClause(*iteratorForAffectedClauseIds, my_clauseDB, my_umap);
        }
    }

    int complementUnitVar = var * -1;
    if (my_umap.find(complementUnitVar) != my_umap.end()) {

        unordered_set<int> listOfAffectedClauses = my_umap[complementUnitVar];
        unordered_set<int>::iterator iteratorForAffectedClauseIds;
        for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
                iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
            Clause& affectedClause = deleteVarFromClause(complementUnitVar, *iteratorForAffectedClauseIds, my_clauseDB,
                    my_umap);

            if (affectedClause.isSingleVariableClause()) { //after deletion of var, the clause has now become unit-var
                int remainingVar = affectedClause.getUnitVar();
                my_unitClause.insert(remainingVar);
                deleteClause(*iteratorForAffectedClauseIds, my_clauseDB, my_umap);
            }
        }
    }
}

bool DPLLAlgo::split(int var, bool isDebug, int recursionDepth) {

    if (isDebug) {
        cout << "[Depth=" << (recursionDepth - 1) << "]Splited on = " << var << endl << std::flush;
    }

    //first clone umap, clauseDB and unitClause
    unordered_map<int, Clause> my_clauseDB = clauseDB;
    unordered_map<int, unordered_set<int>> my_umap = umap;
    unordered_set<int> my_unitClause = unitClause; //as part of singlepolar variable reduction, unitClause may be generated

    setVariableToTrue(var, isDebug, my_clauseDB, my_umap, my_unitClause);

    DPLLAlgo algoForNextRecursion(algo, typeOfBiPolarHeuristic, isLookAheadUnitPropStepEnabled, my_clauseDB, my_umap,
            my_unitClause);
    if (true == algoForNextRecursion.runDPLLAlgo(isDebug, recursionDepth)) {
        satResult.push_back(var);
        list<int>& res = algoForNextRecursion.getSatResult();
        list<int>::iterator resIt;
        for (resIt = res.begin(); resIt != res.end(); resIt++) {
            satResult.push_back(*resIt);
        }
        return (true);
    }

    return (false);
}

//MOMS heuristic
int DPLLAlgo::momsHeuristic(bool isDebug) const {

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
                cout << "<MOMS> Vars impacting maximally " << (itr6->first) << " clauses:";
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
                    return ((*itr7) * -1); //intention is to trigger as much as possible reduction of clauses (not removal of clause)
                }
            }

        }

    }

    assert(false);
    return (0);
}

int DPLLAlgo::biPolarityHeuristic(bool isDebug) const {
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

    int candidateVar =
            (varsWithMaxOccur.front().positiveCount > varsWithMaxOccur.front().negativeCount) ?
                    (varsWithMaxOccur.front().var * -1) : varsWithMaxOccur.front().var; //intention is to trigger as much as possible reduction of clauses (not removal of clause)
    if (varsWithMaxOccur.size() > 0) {
        //TODO tie break;

    }

    return (candidateVar);
}

int DPLLAlgo::maxUnitPropTriggerHeuristic(bool isDebug) {

    assert(true == isLookAheadUnitPropStepEnabled);

    int maxUnitPropTrigger = -1;
    int correspondingVar = 0;
    if (isDebug) {
        cout << "[maxUnitPropTriggerHeuristic]";
    }
    unordered_map<int, int>::iterator it;
    for (it = splitVarToUnitPropFreq.begin(); it != splitVarToUnitPropFreq.end(); it++) {
        if (it->second > maxUnitPropTrigger) {
            maxUnitPropTrigger = it->second;
            correspondingVar = it->first;
        }
        if (isDebug) {
            cout << "(" << it->first << "," << it->second << ") ";
        }
    }

    //as we choose only subset of variables for unitProp, it may so happen none of the variable is
    //eligible for split. In that case, we have no other way than fall back on MOMS
    if (0 == correspondingVar) {
        if (isDebug) {
            cout << endl << "No var is eligble for split" << endl;
        }
        correspondingVar = momsHeuristic(isDebug);
    }

    if (isDebug) {
        cout << endl << "chosen var = " << correspondingVar << endl << std::flush;
    }
    return (correspondingVar);

}

bool DPLLAlgo::lookAheadUnitPropagate(bool isDebug) {

    //We are first pulling out information regarding which variables to look for
    //THis is because we need to access same umap for deleting them - thus these steps cannot be combined under same pass of iterator
    list<int> varToConsider;
    unordered_map<int, unordered_set<int>>::iterator it;
    for (it = umap.begin(); it != umap.end(); it++) {
        int var = it->first;
        if (var < 0) {
            continue;
        }
        varToConsider.push_back(it->first);
    }

    int lookAheadSkipedDueToAbsenceOfBipolarity = 0;
    int varListSize = varToConsider.size();
    while (!varToConsider.empty()) {
        int var = varToConsider.front();
        varToConsider.pop_front();

        if ((umap.find(var) == umap.end()) || (umap.find(var * -1) == umap.end())) {
            lookAheadSkipedDueToAbsenceOfBipolarity++;
            continue;
        }

        //first clone umap, clauseDB and unitClause
        unordered_map<int, unordered_set<int>> my_umapVar = umap;
        unordered_map<int, Clause> my_clauseDBVar = clauseDB;
        unordered_set<int> my_unitClauseVar;

        setVariableToTrue(var, isDebug, my_clauseDBVar, my_umapVar, my_unitClauseVar);

        DPLLAlgo algoForNextRecursion_var(algo, NONE, false, my_clauseDBVar, my_umapVar, my_unitClauseVar);
        bool unitPropResVar = (my_unitClauseVar.size() <= 0) ? true : algoForNextRecursion_var.unitPropagate(false);

        unordered_map<int, unordered_set<int>> my_umapVarNot = umap;
        unordered_map<int, Clause> my_clauseDBVarNot = clauseDB;
        unordered_set<int> my_unitClauseVarNot;

        setVariableToTrue(var * -1, isDebug, my_clauseDBVarNot, my_umapVarNot, my_unitClauseVarNot);

        DPLLAlgo algoForNextRecursion_varNot(algo, NONE, false, my_clauseDBVarNot, my_umapVarNot, my_unitClauseVarNot);
        bool unitPropResVarNot =
                (my_unitClauseVarNot.size() <= 0) ? true : algoForNextRecursion_varNot.unitPropagate(false);

        if ((!unitPropResVar) && (!unitPropResVarNot)) {
            if (isDebug) {
                cout << "[lookAheadUnitPropagate]Variable = " << var << " both polarity conflict" << endl << std::flush;
            }
            return (false);
        }

        if (!unitPropResVar) {
            if (isDebug) {
                cout << "[lookAheadUnitPropagate]Variable = " << var << " positive conflict" << endl << std::flush;
            }
            setVariableToTrue(var * -1, isDebug, clauseDB, umap, unitClause);
            //we are applying unit propagate here itself to get opportunity to skip some variables (if any) due to absence of bi-polarity
            //Additionally, it will reduce the formula if opportunity arises
            unitPropagate(false);
            satResult.push_back(var * -1);
        } else if (!unitPropResVarNot) {
            if (isDebug) {
                cout << "[lookAheadUnitPropagate]Variable = " << var << " negative conflict" << endl << std::flush;
            }
            setVariableToTrue(var, isDebug, clauseDB, umap, unitClause);
            //we are applying unit propagate here itself to get opportunity to skip some variables (if any) due to absence of bi-polarity
            //Additionally, it will reduce the formula if opportunity arises
            unitPropagate(false);
            satResult.push_back(var);
        } else {
            //TODO: local learning for variables with truth values in both polarity
            splitVarToUnitPropFreq[var] = algoForNextRecursion_var.unitClauseReductionCount;
            splitVarToUnitPropFreq[var * -1] = algoForNextRecursion_varNot.unitClauseReductionCount;
        }
    }

    if (isDebug) {
        cout << "[lookAheadUnitPropagate]varListSize = " << varListSize << " lookAheadSkipedDueToAbsenceOfBipolarity="
                << lookAheadSkipedDueToAbsenceOfBipolarity << endl << std::flush;
    }
    return (true);
}

bool DPLLAlgo::removeSingularPolarityVars(bool isDebug) {

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
            deleteClause(*iteratorForAffectedClauseIds, clauseDB, umap);
        }

        loopCount++;
    }

    return ((loopCount > 0) ? true : false);
}

bool DPLLAlgo::unitPropagate(bool isDebug) {
    if (unitClause.size() > 0) {
        unordered_set<int>::iterator entryUnitClauseIt;
        for (entryUnitClauseIt = unitClause.begin(); entryUnitClauseIt != unitClause.end(); entryUnitClauseIt++) {
            //Ensure any unit clause handled is retained as history in conflictDetectorForUnitClause
            //This can be understood better by following example [2 -1][2 1] clauses where suppose in previous level split happened using -2
            //Thus current level will encounter [-1] and [1] as two unit clauses in 'unitClause' list. But if we don't retain
            //conflictDetectorForUnitClause[1] entry in history (even though 1 is handled as part of unit clause),
            //-1 will not be able to find out conflict as conflictDetectorForUnitClause[1] is not retained

            conflictDetectorForUnitClause.insert(*entryUnitClauseIt); //usage of set for unitClause will gurantee non-duplicated entry,
            //additionally conflictDetectorForUnitClause itself is set

            if (conflictDetectorForUnitClause.find((*entryUnitClauseIt) * -1) != conflictDetectorForUnitClause.end()) {
                if (isDebug) {
                    cout << "conflict detected through unit clause for " << (*entryUnitClauseIt) << endl << std::flush;
                }
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

        int unitVar = *(unitClause.begin());
        unitClause.erase(unitVar);

        int complementUnitVar = unitVar * -1;

        satResult.push_back(unitVar);
        unitClauseReductionCount++;

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
                deleteClause(*iteratorForAffectedClauseIds, clauseDB, umap);
            }
        }

        if (umap.find(complementUnitVar) != umap.end()) {
            //Caution: do not use reference for listOfAffectedClauses. If we do so, we may land up in deleting from the same list
            //within deleteClause() which is being accessed (by reference) for iteration of affected clause
            unordered_set<int> listOfAffectedClauses = umap[complementUnitVar]; //!!! CAUTION: if complementUnitVar is not present, umap[complementUnitVar] will insert that key
            unordered_set<int>::iterator iteratorForAffectedClauseIds;
            for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
                    iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
                Clause& affectedClause = deleteVarFromClause(complementUnitVar, *iteratorForAffectedClauseIds, clauseDB,
                        umap);

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
                        return (false); //conflict
                    }

                    unitClause.insert(remainingVar); //due to usage of set, it is guranteed to insert only non duplicated entries
                    conflictDetectorForUnitClause.insert(remainingVar); //due to usage of set, it is guranteed to insert only non duplicated entries
                    deleteClause(*iteratorForAffectedClauseIds, clauseDB, umap);
                }
            }
        }
    }

    return (true);
}

bool DPLLAlgo::runDPLLAlgo(bool isDebug, int recursionDepth) {

    if (isDebug) {
        cout << "[Depth=" << recursionDepth << "]Initially - Clause count = " << clauseDB.size() << " variable count = "
                << umap.size() << endl;
        printDebugInfo(recursionDepth, clauseDB, unitClause);
        printVarToClauseMapping(umap);
    }

    int originalUnitClauseSize = unitClause.size();
    if (!unitPropagate(isDebug)) {
        return (false); //conflict detected
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

    bool lookAheadUnitProp = (!isLookAheadUnitPropStepEnabled) ? true : lookAheadUnitPropagate(isDebug);
    if (!lookAheadUnitProp) {
        return (false);
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
            return (unitPropagate(isDebug));
        }
        return (true); //SAT
    }

    int splitVar = chooseSplitVarAccordingtoHeuristic(isDebug);
    if (0 == splitVar) {
        return (false);
    }

    if (split(splitVar, isDebug, recursionDepth + 1)) {
        return (true);
    }

    if (split(splitVar * -1, isDebug, recursionDepth + 1)) {
        return (true);
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
    unordered_set<int> unitClause; //if any
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
    unordered_set<int>& getListOfUnitClausesIfAny() {
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
        unitClause.insert(c.getUnitVar());
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

void runAlgoForComparativeStudy(HeuristicAlgo algo, BiPolarityHeuristic bipolarHeuristic, const char* alogID,
        ofstream& timingOut, ofstream& resultOut, DimacsParser& dimParser) {

    int maxVarCount = dimParser.getMaxVarCount();

    //As original inputs will mutated within runDPLLAlgo(), will be cloning the original content from dimParser
    unordered_map<int, Clause> originalClauses = dimParser.getClauses();
    unordered_map<int, unordered_set<int>> originalVarToClauseMapping = dimParser.getVarToClauseMapping();
    unordered_set<int> originalUnitClauses = dimParser.getListOfUnitClausesIfAny();

    long long microseconds = -1;
    auto start = std::chrono::high_resolution_clock::now();

    DPLLAlgo dpLLAlgo(algo, bipolarHeuristic, false, originalClauses, originalVarToClauseMapping, originalUnitClauses);
    resultOut << alogID << " ";
    if (dpLLAlgo.runDPLLAlgo(false, 0)) {

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
                //cout << '[' << i << "] ";
                resultOut << i << " ";
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

    timingOut << microseconds << ',';
}

void comparativeStudyOfHeuristics(FILE* in, ofstream& timingOut, ofstream& resultOut) {
    try {
        DimacsParser dimParser;
        dimParser.parse(in, false);
        runAlgoForComparativeStudy(MOMS, NONE, "MOMS", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, SUM, "BIPOLAR-SUM", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, DIFF, "BIPOLAR-DIFF", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, PRODUCT, "BIPOLAR-PROD", timingOut, resultOut, dimParser);
        runAlgoForComparativeStudy(BI_POLARITY_STAT, MAX, "BIPOLAR-MAX", timingOut, resultOut, dimParser);
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
        BiPolarityHeuristic biPolarHeuSubType, bool isLookAheadResolveEnabled, bool crossValidateToBeDone) {
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
        unordered_set<int> originalUnitClauses = dimParser.getListOfUnitClausesIfAny();

        long long microseconds = -1;
        auto start = std::chrono::high_resolution_clock::now();

        DPLLAlgo dpLLAlgo(algo, biPolarHeuSubType, isLookAheadResolveEnabled, originalClauses,
                originalVarToClauseMapping, originalUnitClauses);

        if (dpLLAlgo.runDPLLAlgo(debug, 0)) {

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
 * -l : enables lookahead unit propagate
 * -c : cross validates the SAT output by putting it in original formula.
 * -h : changes heuristic (e.g. MOMS, BI_POLARITY_STAT and MAX_UNIT_PROP_TRIGGER)
 *      if BI_POLARITY_STAT is enabled it expects additional options of SUM, DIFF, PRODUCT or MAX
 *************************************************************/

int main(int argc, char *argv[]) {

    bool debug = false;
    bool isTimingToBePrinted = false;
    bool isDirectoryMode = false;

    char* dir = NULL;
    HeuristicAlgo algo = MOMS;
    BiPolarityHeuristic biPolarHeuSubType = NONE;
    bool isLookAheadEnabled = false;
    bool crossValidateToBeDone = false;
    bool autoCompareMode = false;

    if (argc > 1) {
        for (int i = 1; i < argc; i++) {
            if (0 == strcmp("-d", argv[i])) {
                debug = true;
            } else if (0 == strcmp("-t", argv[i])) {
                isTimingToBePrinted = true;
            } else if (0 == strcmp("-a", argv[i])) {
                autoCompareMode = true;
            } else if (0 == strcmp("-l", argv[i])) {
                isLookAheadEnabled = true;
            } else if (0 == strcmp("-c", argv[i])) {
                crossValidateToBeDone = true;
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
                } else if (0 == strcmp("MAX_UNIT_PROP_TRIGGER", heuristic)) {
                    algo = MAX_UNIT_PROP_TRIGGER;
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
            determineSATOrUNSAT(file, debug, isTimingToBePrinted, algo, biPolarHeuSubType, isLookAheadEnabled,
                    crossValidateToBeDone);
            fclose(file);
        }

    } else {
        if (!determineSATOrUNSAT(stdin, debug, isTimingToBePrinted, algo, biPolarHeuSubType, isLookAheadEnabled,
                crossValidateToBeDone)) {
            cerr << "determineSATOrUNSAT failed from stdin";
            return (1);
        }
    }

    return (0);
}

