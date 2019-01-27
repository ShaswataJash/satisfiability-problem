//============================================================================
// Name        : DPLLCppSingleFileUsingSTL.cpp
// Author      : Shaswata Jash
// Version     :
// Copyright   : Your copyright notice
// Description : Hello World in C++, Ansi-style
//============================================================================

#include <iostream>
#include <stdexcept>
#include <cstring>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <list>
#include <chrono>
#include <cassert>
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
    MOMS,
    MAX_PRODUCT_POLARITY
}HeuristicAlgo;

class DPLLAlgo {
private:

    HeuristicAlgo algo;

    //For all the below three reference variable, data in them will be changed (majorly deleted but for unitClause, elements
    // can be added too) - thus caller of runDPLLAlgo() should rely sanctity of these variables after return from the functions.
    unordered_map<int, Clause>& clauseDB; //map of unique clause-id to actual clauses
    unordered_map<int, unordered_set<int>>& umap; //map of variable to list of clause-id (each clause is assigned unique id)
    unordered_set<int>& unitClause; //due to usage of set, it will gurantee non-duplicate entry

    unordered_set<int> conflictDetectorForUnitClause;
    list<int> satResult;

    int momsHeauristic(bool isDebug) const;
    int maxProductPolarityHeuristic(bool isDebug) const;
    int chooseSplitVarAccordingtoHeuristic(bool isDebug) const{

        switch(algo){
        case MOMS: return (momsHeauristic(isDebug));
        case MAX_PRODUCT_POLARITY: return (maxProductPolarityHeuristic(isDebug));
        }
        assert(false);
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

    static void printCurrentUnitClauseQueue(unordered_set<int>& unitClause);
    static void printDebugInfo(int recursionDepth, unordered_map<int, Clause>& clauseDB,
            unordered_set<int>& unitClause);
    static void printVarToClauseMapping(unordered_map<int, unordered_set<int>>& my_umap);

    bool split(int var, bool isDebug, int recursionDepth, bool singlePolarityRemoval);
    bool removeSingularPolarityVars(bool isDebug);
    bool unitPropagate(bool isDebug);
public:
    bool runDPLLAlgo(bool isDebug, int recursionDepth, bool singlePolarityRemoval);

    list<int>& getSatResult() {
        return (satResult);
    }

    DPLLAlgo(HeuristicAlgo my_algo, unordered_map<int, Clause>& my_clauseDB, unordered_map<int, unordered_set<int>>& my_umap,
            unordered_set<int>& my_unitClause) :
                algo(my_algo), clauseDB(my_clauseDB), umap(my_umap), unitClause(my_unitClause) {
    }

};

void DPLLAlgo::printCurrentUnitClauseQueue(unordered_set<int>& my_unitClause) {
    unordered_set<int>::iterator singleClauseIt;
    cout << "[S:";
    for (singleClauseIt = my_unitClause.begin(); singleClauseIt != my_unitClause.end(); singleClauseIt++) {
        cout << *singleClauseIt << ',';
    }
    cout << ']';
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

bool DPLLAlgo::split(int var, bool isDebug, int recursionDepth, bool singlePolarityRemoval) {

    if (isDebug) {
        cout << "[Depth=" << (recursionDepth - 1) << "]Splited on = " << var << endl << std::flush;
    }

    //first clone umap, clauseDB and unitClause
    unordered_map<int, unordered_set<int>> my_umap = umap;
    unordered_map<int, Clause> my_clauseDB = clauseDB;
    assert(0 == unitClause.size());
    unordered_set<int> my_unitClause;

    assert(my_umap.find(var) != my_umap.end()); //as removeSingularPolarityVars() has removed single polarity vars

    //Caution: do not use reference for listOfAffectedClauses. If we do so, we may land up in deleting from the same list
    //within deleteClause() which is being accessed (by reference) for iteration of affected clause
    unordered_set<int> listOfAffectedClauses = my_umap[var];
    unordered_set<int>::iterator iteratorForAffectedClauseIds;
    for (iteratorForAffectedClauseIds = listOfAffectedClauses.begin();
            iteratorForAffectedClauseIds != listOfAffectedClauses.end(); iteratorForAffectedClauseIds++) {
        deleteClause(*iteratorForAffectedClauseIds, my_clauseDB, my_umap);
    }

    int complementUnitVar = var * -1;
    assert(my_umap.find(complementUnitVar) != my_umap.end()); //if complement not found, this split var has single polarity - this is not candidate for split

    listOfAffectedClauses = my_umap[complementUnitVar];
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

    DPLLAlgo algoForNextRecursion(algo, my_clauseDB, my_umap, my_unitClause);
    if (true == algoForNextRecursion.runDPLLAlgo(isDebug, recursionDepth, singlePolarityRemoval)) {
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
int DPLLAlgo::momsHeauristic(bool isDebug) const {

    //STAGE1: First create map for size of clause to clause-id mapping
    map<int, list<int>> sizeToClauseIdMapping; //it will be default ordered in ascending (i.e. lower size clauses to higher ones)
    unordered_map<int, Clause>::iterator itr1;
    for (itr1 = clauseDB.begin(); itr1 != clauseDB.end(); itr1++) {
        sizeToClauseIdMapping[(itr1->second).getVariablesListSize()].push_back((itr1->second).getUniqueID());
    }

    map<int, list<int>>::iterator itr2 ;
    for( itr2 = sizeToClauseIdMapping.lower_bound(2); itr2 != sizeToClauseIdMapping.end(); itr2 ++){ //start iterate only from size 2
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
        for(itr6 =  occurenceFreToVarMap.begin(); itr6 != occurenceFreToVarMap.end(); itr6++){
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
            int productPolarityMetric = 0;
            int chosenVar = 0;
            for (itr7 = varsWithMaxOccur.begin(); itr7 != varsWithMaxOccur.end(); itr7++) {
                //STAGE tie-breaking
                if ((umap.find(*itr7) != umap.end()) && (umap.find((*itr7) * -1) != umap.end())) {
                    int currentProduct = umap[*itr7].size() * umap[(*itr7) * -1].size();
                    if(currentProduct > productPolarityMetric){
                        chosenVar = *itr7;
                        productPolarityMetric = currentProduct;
                    }
                }
            }

            if(productPolarityMetric > 0){
                return (chosenVar * -1); //intention is to trigger as much as possible reduction of clauses (not removal of clause)
            }

        }

    }

    assert(false);
    return (0);
}

int DPLLAlgo::maxProductPolarityHeuristic(bool isDebug) const {
    typedef struct polarityStat {
        int positiveCount;
        int negativeCount;
        int var;
    } polarityStat;
    unordered_map<int, unordered_set<int>>::iterator itr1;
    map<int, list<polarityStat>, greater<int>> occurenceFreToVarMap; //descending order storage
    for (itr1 = umap.begin(); itr1 != umap.end(); itr1++) {
        if (((itr1->first > 0) && (itr1->second).size() > 0)) {

            if (umap.find((itr1->first) * (-1)) != umap.end()) {
                polarityStat ps;
                ps.positiveCount = (itr1->second).size();
                ps.negativeCount = umap[(itr1->first) * (-1)].size();
                ps.var = itr1->first;
                int reverse_polarity_occur = umap[(itr1->first) * (-1)].size() * (itr1->second).size();
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
                    varsWithMaxOccur.front().var : (varsWithMaxOccur.front().var * -1);
    if (varsWithMaxOccur.size() > 0) {
        //TODO tie break;

    }

    return (candidateVar); //intention is both together as much clause is removed, simultaneously reduction happens - thus product is matrices instead of sum
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
        int unitVar = *(unitClause.begin());
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

        if (isDebug) {
            printCurrentUnitClauseQueue(unitClause);
            cout << endl << std::flush;
        }
    }

    return (true);
}

bool DPLLAlgo::runDPLLAlgo(bool isDebug, int recursionDepth, bool singlePolarityRemoval) {

    if (isDebug) {
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
        cout << "After unit clause reduction - " << "Clause count = " << clauseDB.size() << " variable count = "
                << umap.size() << endl;
        printDebugInfo(recursionDepth, clauseDB, unitClause);
        printVarToClauseMapping(umap);
    }

    if(singlePolarityRemoval){
        bool singlePolarReduction = removeSingularPolarityVars(isDebug);
        if (isDebug && singlePolarReduction) {
            cout << "After single Polar reduction - " << "Clause count = " << clauseDB.size() << " variable count = "
                    << umap.size() << endl;
            printDebugInfo(recursionDepth, clauseDB, unitClause);
            printVarToClauseMapping(umap);
        }
    }

    int splitVar = chooseSplitVarAccordingtoHeuristic(isDebug);

    if (split(splitVar, isDebug, recursionDepth + 1, singlePolarityRemoval)) {
        return (true);
    }

    if (split(splitVar * -1, isDebug, recursionDepth + 1, singlePolarityRemoval)) {
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

bool determineSATOrUNSAT(FILE* in, bool debug, bool isTimingToBePrinted, bool singlePolarityRemoval, HeuristicAlgo algo) {
    try {

        DimacsParser dimParser;
        dimParser.parse(in, debug);
        int maxVarCount = dimParser.getMaxVarCount();

        if (debug) {
            cout << "maxVarCount = " << maxVarCount << " maxClauseCount = " << dimParser.getMaxClauseCount() << endl;
        }

        long long microseconds = -1;
        auto start = std::chrono::high_resolution_clock::now();

        DPLLAlgo dpLLAlgo(algo, dimParser.getClauses(), dimParser.getVarToClauseMapping(),
                dimParser.getListOfUnitClausesIfAny());

        if (dpLLAlgo.runDPLLAlgo(debug, 0, singlePolarityRemoval)) {

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
                    cout << '[' << i << "] ";
                }
            }
            delete[] finalFormattedResult;
            cout << "0" << std::flush;
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

int main(int argc, char *argv[]) {

    bool debug = false;
    bool isTimingToBePrinted = false;
    bool isDirectoryMode = false;
    bool singlePolarityRemoval = false;
    char* dir = NULL;
    HeuristicAlgo algo = MOMS;

    if (argc > 1) {
        for (int i = 1; i < argc; i++) {
            if (0 == strcmp("-d", argv[i])) {
                debug = true;
            } else if (0 == strcmp("-t", argv[i])) {
                isTimingToBePrinted = true;
            } else if (0 == strcmp("-dir", argv[i])) {
                isDirectoryMode = true;
                dir = argv[i + 1];
            } else if (0 == strcmp("-p", argv[i])) {
                singlePolarityRemoval = true;
            } else if (0 == strcmp("-h", argv[i])) {
                char* heuristic = argv[i + 1];
                if(0 == strcmp("MOMS", heuristic)){
                    algo = MOMS;
                } else if (0 == strcmp("MAX_PRODUCT_POLARITY", heuristic)) {
                    algo = MAX_PRODUCT_POLARITY;
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
        list<string>::iterator it;
        for (it = files.begin(); it != files.end(); it++) {
            cout << *it << endl << std::flush;
            FILE* file = fopen((*it).c_str(), "r");
            determineSATOrUNSAT(file, debug, isTimingToBePrinted, singlePolarityRemoval, algo);
            fclose(file);
        }

    } else {
        if (!determineSATOrUNSAT(stdin, debug, isTimingToBePrinted, singlePolarityRemoval, algo)) {
            cerr << "determineSATOrUNSAT failed from stdin";
            return (1);
        }
    }

    return (0);
}

