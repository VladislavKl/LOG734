#include <iostream>
#include <fstream>
#include <vector>
#include <cstring>
#include <limits>
#include <iomanip>
#include <algorithm>
#include <bitset>
#include "time.h"
#include <cmath>

const std::vector<std::string> FILES{"100-5-01.txt","100-5-02.txt", "100-5-03.txt", "100-5-04.txt", "100-5-05.txt",
                                     "250-10-01.txt","250-10-02.txt","250-10-03.txt","250-10-04.txt","250-10-05.txt",
                                     "500-30-01.txt","500-30-02.txt","500-30-03.txt","500-30-04.txt","500-30-05.txt"
};

const std::vector<int> BEST_INIT_SOL_IN_PREV_YEARS{24285, 24274, 23317, 23102, 23826, 58697, 58145, 57613, 60425,
                                                   57643, 114878, 113760, 115625, 113853, 115226};

const std::vector<int> BEST_IMP_SOL_IN_PREV_YEARS{24381, 24274, 23496, 23389, 23991, 59021, 58629, 57868, 60875,
                                                  57886, 115440, 114246, 116228, 114844, 115928};

const std::vector<int> BEST_META_SOL_IN_PREV_YEARS{24381, 24274, 23676, 23534, 23991, 59139, 58785, 57835, 60896,
                                                  58008, 115511, 114305, 116228, 114843, 115928};


const int MAX_PROBLEM_SIZE = 500;
typedef std::bitset<MAX_PROBLEM_SIZE> Solution;

enum NEIGHBOURHOOD_OPERATOR {
    FLIP,
    DOUBLE_FLIP,
    TRIPLE_FLIP,
    QUAD_FLIP,
    DOUBLE_SWAP,
    DOUBLE_SWAP_SWAP,
    DOUBLE_FLIP_SWAP,
    SWAP
};

struct Candidate    {
    Candidate(): i(-1), weight(0) {}
    Candidate(int j, double w): i(j), weight(w) {}
    int i;
    double weight;
};


//read function from lectures
bool readInstance(std::string &filename, std::vector<int>& c,
                  std::vector<std::vector<int> >& a, std::vector<int>& b,
                  int &n, int &m, int &q, int &opt) {
    bool success = true;
    // clear vectors, in case they are being re-occupied: c.clear();
    a.clear();
    b.clear();
    c.clear();
    // open the file:
    std::ifstream file(filename.c_str());
    if (!file.is_open()) {
        // failed to open file, so make sure to indicate this when we return:
        success = false;
    } else {
        // file is open and we are ready to read:
        int temp;
        file >> n >> m >> q >> opt;
        // read the objective function coefficients (there are n of them):
        for (int j = 0; j < n; ++j) {
            file >> temp;
            c.push_back(temp);
        }
        // resize a, so that we can fit each of the lhs of the constraints there:
        a.resize(m);
        // now, read the left hand sides of each constraint:
        for (int i = 0; i < m; ++i) {
            // read the lhs coefficients for each variable:
            for (int j = 0; j < n; ++j) {
                file >> temp;
                a[i].push_back(temp);
            }
        }
        // now read the right hand sides:
        for (int i = 0; i < m; ++i) {
            file >> temp;
            b.push_back(temp);
        }
    }
    // return true if file was opened, and false otherwise:
    return success;
}

//returns index of the element with max weight
int idxMax(const int& n, std::vector<double>& weight, std::vector<int>& x) {
    int idx = 0; // index of the max weight element
    double max = -std::numeric_limits<double>::max(); //the value of max element
    for (int i = 0; i < n; ++i) {
        if (x[i] == -1 && weight[i] > max) {
            max = weight[i];
            idx = i;
        }
    }
    return idx;
}

//assigns weights to all the variables
void getWeight(const int &n, const int &m, std::vector<int>& c,
               std::vector<std::vector<int>> &a, std::vector<int>& b,
               std::vector<int>& occupied,
               std::vector<double>& weight) {

    for (int i = 0; i < n; ++i) {
        bool isWithinLimits = true;
        double trick = 0;
        for (int j = 0; j < m; ++j) {
            if (occupied[j] + a[j][i] <= b[j]) {
                trick +=
                        double(a[j][i])
                        / (
                                (double(b[j]) - double(occupied[j]))*
                                (double(b[j]) - double(occupied[j]))     // we square the slacks
                        );
            } else {
                isWithinLimits = false;
                break;
            }
        }
        weight[i] = isWithinLimits ? (c[i] / trick) : 0;
    }
}

bool checkSolutionFeasibility(const int&n, const int&m, std::vector<int>& x, std::vector<std::vector<int>>& a,
                              std::vector<int>& b)  {
    for (int i = 0; i < m; ++i) {
        int row_activity = 0;
        for (int j = 0; j < n; ++j)
            row_activity += x[j] ? a[i][j] : 0;
        if (row_activity > b[i])
            return false;
    }
    return true;
}


void computeSolutionRowActivities(const int&n, const int&m, const Solution& x,
                                  std::vector<std::vector<int>>& a,
                                  std::vector<int>& b, std::vector<int>& row_activities)    {
    for (int i = 0; i < m; ++i) {
        row_activities[i] = 0;
        for (int j = x._Find_first(); j < n; j = x._Find_next(j))
            row_activities[i] += a[i][j];
    }
}


bool checkSolutionFeasibility(const int&n, const int&m, const Solution& x, std::vector<std::vector<int>>& a,
                              std::vector<int>& b)  {
    std::vector<int> row_activity(m);
    computeSolutionRowActivities(n, m, x, a, b, row_activity);
    for (int i = 0; i < m; ++i)
        if (row_activity[i] > b[i])
            return false;
    return true;
}

inline int compute_flip_direction(const Solution&x, int i) {
    return (i < 0) ? 0 : (x.test(i) ? -1 : 1);
}



bool checkSolutionFeasibilityAfterPerturbing(const int&n, const int&m, const Solution& x,
                                             std::vector<std::vector<int>>& a,
                                             std::vector<int>& b, std::vector<int>& row_activity, int first,
                                             int second = -1, int third = -1, int fourth = -1)  {

    int dir_1 = compute_flip_direction(x, first);
    int dir_2 = compute_flip_direction(x, second);
    int dir_3 = compute_flip_direction(x, third);
    int dir_4 = compute_flip_direction(x, fourth);
    for (int i = 0; i < m; ++i)
        if ((row_activity[i] + a[i][first]*dir_1 + ((second < 0) ? 0 : a[i][second])*dir_2
             + ((third < 0) ? 0 : a[i][third])*dir_3
             + ((fourth < 0) ? 0 : a[i][fourth])*dir_4) > b[i])
            return false;
    return true;
}

/*bool checkSolutionFeasibilityAfterPerturbing_old(const int&n, const int&m, const Solution& x,
                                             std::vector<std::vector<int>>& a,
                                             std::vector<int>& b, std::vector<int>& row_activity,
                                             NEIGHBOURHOOD_OPERATOR N_operator, int first, int second = -1,
                                             int third = -1, int fourth = -1)  {

    bool direction = x.test(first);
    bool direction_second = x.test(second); // if we are swapping, go opposite from the first variable
    bool direction_third = x.test(third);
    bool direction_fourth = x.test(fourth);
    switch (N_operator) {
        case FLIP: {
            for (int i = 0; i < m; ++i)
                if ((direction ? row_activity[i] - a[i][first] : row_activity[i] + a[i][first]) > b[i])
                    return false;
            break;
        }

        case DOUBLE_FLIP:
        case SWAP:  {
            for (int i = 0; i < m; ++i)
                if (direction ? row_activity[i] - a[i][first] + (direction_second ? -a[i][second] : a[i][second]) :
                    row_activity[i] + a[i][first] + (direction_second ? -a[i][second] : a[i][second]) > b[i])
                    return false;
            break;
        }

        case DOUBLE_SWAP:  {
            for (int i = 0; i < m; ++i) {
                int act = direction ? row_activity[i] - a[i][first] : row_activity[i] + a[i][first];
                act = direction_second ? act - a[i][second] : act + a[i][second];
                act = direction_third ? act - a[i][third] : act + a[i][third];
                act = direction_fourth ? act - a[i][fourth] : act + a[i][fourth];
                if (act > b[i])
                    return false;
            }
            break;
        }
    }

    return true;
}*/


//solution
double constructionHeuristic(const int& n, const int& m, std::vector<int>& x, std::vector<int>& c,
                             std::vector<std::vector<int>>& a, std::vector<int>& b) {

    clock_t start = clock(); //start time

    std::vector<int> occupied(m); //the space occupied in each dimension
    std::vector<double> weight(n); //weight to choose variable with argmax
    int nassigned = 0; //number of assigned variables
    occupied.clear(); // in case it is not the first call

    //start algorithm
    while (nassigned < n) { //while all variables are not assigned with 0 or 1
        getWeight(n, m, c, a, b, occupied, weight); //assigning weights for each variable
        int j = idxMax(n, weight, x); //index of argmax weight element

        bool isWithinLimits = true; //check if variable is included in objective function, the bounds are not violated
        for (int i = 0; i < m; ++i) {
            if (occupied[i] + a[i][j] > b[i]) {
                isWithinLimits = false;
                break;
            }
        }

        ++nassigned;
        if (isWithinLimits) {
            x[j] = 1;
            for (int i = 0; i < m; ++i) {
                occupied[i] += a[i][j];     //space is occupied by variable, as it is added to the objective function
            }
        } else {
            x[j] = 0; //variable don't suit as it violates the boundaries, thus, not included in the objective function
        }
    }

    return (clock() - start) / double(CLOCKS_PER_SEC / 1000 ); //time in milliseconds spent on processing
    // (now time - start time)
}

int computeSolutionObjective(const int &n, const std::vector<int>&c, const Solution& solution) {
    int objectiveValue = 0;
    for (int i = solution._Find_first(); i < n; i = solution._Find_next(i))  {
        objectiveValue += c[i];
    }
    return objectiveValue;
}

bool explore_swap_neighbourhood(const int &n, const int &m,  int init_objective, std::vector<int>& row_activity,
                                bool& neighbour_found, const Solution& x,
                                std::vector<int> &c, std::vector<std::vector<int>>& a,
                                std::vector<int>& b,
                                Solution& neighbour, int& neighbour_objective,
                                bool return_after_first_improvement = false)   {
    int current_objective;
    for (int i = x._Find_first(); i < n; i = x._Find_next(i)) {           // first is one
        int objective_after_first_flip = init_objective - c[i];
        for (int j = 0; j < n; ++j) {
            if (x.test(j))            // second should be zero
                continue;
            if ((current_objective = objective_after_first_flip + c[j]) > neighbour_objective) {
                if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, i, j)) {
                    neighbour = x;
#ifdef DEBUG_INFO
                    printf("Improvement: swap %d: %d and %d: %d \t-- feasible\n", i, x.test(i), j, x.test(j));
#endif
                    neighbour.flip(i);
                    neighbour.flip(j);
                    neighbour_found = true;
                    neighbour_objective = current_objective;
                    if (return_after_first_improvement)
                        return true;
                }
#ifdef DEBUG_INFO
                //                        else
//                            printf("Possible improvement: swap %d: %d and %d: %d \t-- infeasible\n", i, x.test(i), j, x.test(j));
#endif
            }
        }
    }
    return false;
}




bool yieldNeighbour(const int &n, const int &m,  const Solution& x,
                    std::vector<int> &c, std::vector<std::vector<int>>& a,
                    std::vector<int>& b, NEIGHBOURHOOD_OPERATOR N_operator,
                    Solution& neighbour, int& neighbour_objective,
                    bool return_after_first_improvement = false)
{
#ifdef DEBUG_INFO
    freopen("log.out","a+", stdout);
#endif
    bool neighbour_found = false;

    int init_objective = computeSolutionObjective(n, c, x);
    int current_objective;
    neighbour_objective = init_objective;

    std::vector<int> row_activity(m);
    computeSolutionRowActivities(n, m, x, a, b, row_activity);

    switch (N_operator) {

        case FLIP: {
            for (int i = 0; i < n; ++i) {
                if ((current_objective = x.test(i) ? init_objective - c[i] : init_objective + c[i]) > neighbour_objective) {
                    if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, i)) {
                        neighbour = x;
                        neighbour.flip(i);
                        neighbour_found = true;
                        neighbour_objective = current_objective;
                        if (return_after_first_improvement)
                            return true;
                    }
                }
            }
            break;
        }

        case DOUBLE_FLIP_SWAP:
        case DOUBLE_FLIP: {

            for (int i = 0; i < n; ++i) {
                int objective_after_first_flip = x.test(i) ? init_objective - c[i] : init_objective + c[i];
                for (int j = i + 1; j < n; ++j) {
                    if ((current_objective = x.test(j) ? objective_after_first_flip - c[j] :
                                             objective_after_first_flip + c[j]) > neighbour_objective) {
                        if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, i, j)) {
                            neighbour = x;
#ifdef DEBUG_INFO
                            printf("Improvement: double-flip %d: %d and %d: %d \t-- feasible\n", i, x.test(i), j, x.test(j));
#endif
                            neighbour.flip(i);
                            neighbour.flip(j);
                            neighbour_found = true;
                            neighbour_objective = current_objective;
                            if (return_after_first_improvement)
                                return true;
                        }
#ifdef DEBUG_INFO
                        //                        else
//                            printf("Possible improvement: double-flip %d: %d and %d: %d \t-- infeasible\n", i, x.test(i), j, x.test(j));
#endif
                    }
                }
            }
            if (N_operator == DOUBLE_FLIP_SWAP) {
                computeSolutionRowActivities(n, m, neighbour, a, b, row_activity);
                explore_swap_neighbourhood(m, m, neighbour_objective, row_activity, neighbour_found,
                                           neighbour, c, a,
                                           b, neighbour,
                                           neighbour_objective, return_after_first_improvement);

            }
            break;
        }

        case TRIPLE_FLIP: {

            for (int i = 0; i < n; ++i) {
                int objective_after_first_flip = x.test(i) ? init_objective - c[i] : init_objective + c[i];
                for (int j = i + 1; j < n; ++j) {
                    int objective_after_second_flip = x.test(j) ? objective_after_first_flip - c[j] : objective_after_first_flip + c[j];
                    for (int k = j + 1; k < n; ++k) {
                        if ((current_objective = x.test(k) ? objective_after_second_flip - c[k] :
                                                 objective_after_second_flip + c[k]) > neighbour_objective) {
                            if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, i,
                                                                        j, k)) {
                                neighbour = x;
#ifdef DEBUG_INFO
                                printf("Improvement: triple-flip %d: %d and %d: %d \t-- feasible\n", i,
                                       x.test(i), j, x.test(j));
#endif
                                neighbour.flip(i);
                                neighbour.flip(j);
                                neighbour.flip(k);
                                neighbour_found = true;
                                neighbour_objective = current_objective;
                                if (return_after_first_improvement)
                                    return true;
                            }
#ifdef DEBUG_INFO
                            //                        else
//                            printf("Possible improvement: double-flip %d: %d and %d: %d \t-- infeasible\n", i, x.test(i), j, x.test(j));
#endif
                        }
                    }
                }
            }
            break;
        }

        case QUAD_FLIP: {

            for (int i = 0; i < n; ++i) {
                int objective_after_first_flip = x.test(i) ? init_objective - c[i] : init_objective + c[i];
                for (int j = i + 1; j < n; ++j) {
                    int objective_after_second_flip = x.test(j) ? objective_after_first_flip - c[j] : objective_after_first_flip + c[j];
                    for (int k = j + 1; k < n; ++k) {
                        int objective_after_third_flip = x.test(k) ? objective_after_second_flip - c[k] :
                                                         objective_after_second_flip + c[k];
                        for (int l = k + 1; l < n; ++l) {
                            if ((current_objective = x.test(l) ? objective_after_third_flip - c[l] :
                                                     objective_after_third_flip + c[l]) > neighbour_objective) {
                                if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, i,
                                                                            j, k, l)) {
                                    neighbour = x;
#ifdef DEBUG_INFO
                                    printf("Improvement: quad-flip %d: %d and %d: %d \t-- feasible\n", i,
                                           x.test(i), j, x.test(j));
#endif
                                    neighbour.flip(i);
                                    neighbour.flip(j);
                                    neighbour.flip(k);
                                    neighbour.flip(l);
                                    neighbour_found = true;
                                    neighbour_objective = current_objective;
                                    if (return_after_first_improvement)
                                        return true;
                                }
#ifdef DEBUG_INFO
                                //                        else
    //                            printf("Possible improvement: double-flip %d: %d and %d: %d \t-- infeasible\n", i, x.test(i), j, x.test(j));
#endif
                            }
                        }
                    }
                }
            }
            break;
        }

        case SWAP: {
            explore_swap_neighbourhood(m, m, init_objective, row_activity, neighbour_found, x, c, a,
                                       b, neighbour,
                                       neighbour_objective, return_after_first_improvement);
            break;

        }

        case DOUBLE_SWAP_SWAP:
        case DOUBLE_SWAP: {
            for (int i = x._Find_first(); i < n; i = x._Find_next(i)) {
                for (int j = 0; j < n; ++j) {
                    if (x.test(j))            // second should be zero
                        continue;
                    for (int k = x._Find_next(i); k < n; k = x._Find_next(k)) {
                        for (int l = j+1; l < n; ++l) {
                            if (x.test(l))            // second should be zero
                                continue;
                            if ((current_objective = init_objective - c[i] + c[j] - c[k] + c[l]) > neighbour_objective) {
                                if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, i, j, k, l)) {
                                    neighbour = x;
#ifdef DEBUG_INFO
                                    printf("Improvement: double_swap %d: %d and %d: %d \t-- feasible\n", i, x.test(i), j, x.test(j));
#endif
                                    neighbour.flip(i);
                                    neighbour.flip(j);
                                    neighbour.flip(k);
                                    neighbour.flip(l);
                                    neighbour_found = true;
                                    neighbour_objective = current_objective;
                                    if (return_after_first_improvement)
                                        return true;
                                }
#ifdef DEBUG_INFO
                                //                        else
//                            printf("Possible improvement: swap %d: %d and %d: %d \t-- infeasible\n", i, x.test(i), j, x.test(j));
#endif
                            }


                        }
                    }
                }


            }

            if (N_operator == DOUBLE_SWAP_SWAP) {
#ifdef DEBUG_INFO
                printf("Starting additional swap...\n");
#endif
                computeSolutionRowActivities(n, m, neighbour, a, b, row_activity);
                explore_swap_neighbourhood(m, m, neighbour_objective, row_activity, neighbour_found,
                                           neighbour, c, a,
                                           b, neighbour,
                                           neighbour_objective, return_after_first_improvement);

            }
            break;

        }


    }



    return neighbour_found;
}


bool localSearch(const int &n, const int &m,  Solution& initial_solution, std::vector<int> &c,
                 std::vector<std::vector<int>>& a, std::vector<int>& b, Solution& improved_solution, int& improved_objective,
                 double& time_taken, int timeLimit = 30,
                 NEIGHBOURHOOD_OPERATOR N_operator = SWAP,
                 bool first_improvement_heuristic = false) {

    clock_t start = clock();
    bool improvement_found = false;
    Solution starting_point = initial_solution;
    while (yieldNeighbour(n, m, starting_point, c, a, b, N_operator, improved_solution,
                          improved_objective,
                          first_improvement_heuristic))
    {
        starting_point = improved_solution;
        improvement_found = true;
        if ((clock() - start) / double(CLOCKS_PER_SEC) > timeLimit)
            break;
    }


    time_taken = (clock() - start) / double(CLOCKS_PER_SEC / 1000); // time taken by the heuristic in milliseconds

    return improvement_found;
}


double findMax(std::vector<int>& indices, int k, std::vector<double>& weight, double& max) {
    max = weight[indices[0]];
    int maxIdx = 0;

    for (int i = 1; i < k; ++i) {
        if (weight[indices[i]] > max) {
            max = weight[indices[i]];
            maxIdx = i;
        }
    }

    return maxIdx;
}




void createRestrictedCandidateList(const int &n, std::vector<double>& weight, Solution& assigned, int candNumber,
                                   std::vector<int>& restrictedCandidateList) {
    assigned.flip();
    int i = assigned._Find_first();
    std::vector<Candidate> candidate_list(n);
    int k = 0;
    for (; i < n; i=assigned._Find_next(i)) {
        candidate_list[k] = Candidate(i, weight[i]);
        k++;
    }
    std::partial_sort(candidate_list.begin(), candidate_list.begin() + candNumber, candidate_list.begin() + k,
                      [](Candidate& a, Candidate& b) {return a.weight > b.weight;});

    for (i = 0; i < candNumber; ++i)
    {
        restrictedCandidateList[i] = candidate_list.at(i).i;
    }

    assigned.flip();
}

void weightForGRASP(const int &n, const int &m, std::vector<int>& c,
                    std::vector<std::vector<int>> &a, std::vector<int>& b,
                    std::vector<int>& occupied,
                    std::vector<double>& weight) {

    for (int i = 0; i < n; ++i) {
        bool isWithinLimits = true;
        double trick = 0;
        for (int j = 0; j < m; ++j) {
            if (occupied[j] + a[j][i] <= b[j]) {
                trick +=
                        double(a[j][i])
                        / (
                                (double(b[j]) - double(occupied[j]))
                        );
            } else {
                isWithinLimits = false;
                break;
            }
        }
        weight[i] = isWithinLimits ? (c[i] / trick) : 0;
    }
}


void GRASP(const int &n, const int &m, Solution& x, std::vector<int>& c,
           std::vector<std::vector<int>> &a, std::vector<int>& b, double alpha) {

    Solution assigned; //1 if we already assigned value for a variable
    std::vector<int> occupied(m,0); //the space occupied in each dimension
    std::vector<double> weight(n,0); //weight to choose variable with argmax
    int nassigned = 0; //number of assigned variables
    occupied.clear(); // in case it is not the first call
    weight.clear();

    int candNumber;
    std::vector<int> restrictedCandList(n);

    //start algo
    while (nassigned < n) {
        weightForGRASP(n, m, c, a, b, occupied, weight);

        candNumber = ceil(alpha * (n - nassigned));
        createRestrictedCandidateList(n, weight, assigned, candNumber, restrictedCandList);

        srand(time(NULL));
        int j = restrictedCandList[rand() % candNumber];

        bool isWithinLimits = true; //check if variable is included in objective function, the bounds are not violated
        for (int i = 0; i < m; ++i) {
            if (occupied[i] + a[i][j] > b[i]) {
                isWithinLimits = false;
                break;
            }
        }

        ++nassigned;
        assigned[j] = true;
        if (isWithinLimits) {
            x.set(j);
            for (int i = 0; i < m; ++i) {
                occupied[i] += a[i][j];     //space is occupied by variable, as it is added to the objective function
            }
        } else {
            x.reset(j);//variable don't suit as it violates the boundaries, thus, not included in the objective function
        }

    }
}

//void alphaGrasp(const int &n, const int &m, std::vector<int>& x, std::vector<int>& c,
//                std::vector<std::vector<int>> &a, std::vector<int>& b, double alpha, int seconds) {
//    auto start = clock();
//
//    long long sum = 0;
//    int count = 0;
//    int best = -1;
//
//
//    while ((clock() - start) / double(CLOCKS_PER_SEC) < seconds) {
//        count++;
//        std::vector<int> solution(n);
//        GRASP(n, m, solution, c, a, b, alpha);
//
//        Solution b_solution;
//        for (int i = 0; i < n; ++i)
//            b_solution.set(i, solution[i] == 1);
//
//        int cost = computeSolutionObjective(n, c, b_solution);
//        sum += cost;
//        if (cost > best) {
//            best = cost;
//            x = solution;
//        }
//    }
//
//    std::cout << alpha << ' ' << best << '\n';
//
//}

double metaheuristic(const int &n, const int &m, Solution& x, std::vector<int>& c,
                     std::vector<std::vector<int>> &a, std::vector<int>& b, NEIGHBOURHOOD_OPERATOR N_operator = DOUBLE_SWAP,
                     double alpha = 0.07, int LOCAL_SEARCH_LIMIT = 10000, int GRASP_TIME_LIMIT = 20000, int OVERALL_TIME_LIMIT = 59,
                     bool first_improvement_heuristic = false) {
    clock_t start = clock(); //start time
    std::vector<std::pair<Solution, int>> solutions;

    Solution improved_solution;

    Solution solution(n);
    int new_objective;
    double localSearchTime;

    while ((clock() - start) / double(CLOCKS_PER_SEC) < OVERALL_TIME_LIMIT) {
        int best = 0;
        Solution bestSolution;

        auto graspStart = clock();
        while ((clock() - graspStart) / double(CLOCKS_PER_SEC) < GRASP_TIME_LIMIT) {
            GRASP(n, m, solution, c, a, b, alpha);

            int cost = computeSolutionObjective(n, c, solution);

            if (cost > best) {
                best = cost;
                bestSolution = solution;
            }
        }

        localSearch(n, m, bestSolution, c, a, b, improved_solution, new_objective,
                    localSearchTime,LOCAL_SEARCH_LIMIT, N_operator, first_improvement_heuristic);

        solutions.emplace_back(improved_solution, best);
    }

    int bestcost = -1;
    auto bestSol = solutions[0];

    for (const auto &t: solutions) {
        if (t.second > bestcost) {
            bestcost = t.second;
            bestSol = t;
        }
    }

    x = bestSol.first;

    return (clock() - start) / double(CLOCKS_PER_SEC / 1000); //time in milliseconds spent on processing
    // (now time - start time)

}


int main(int argc, char **argv) {
    std::vector<int> c, b;
    std::vector<std::vector<int>> a;
    int n, m, q, opt;
    bool return_after_first_improvement = false;

    NEIGHBOURHOOD_OPERATOR strategy = DOUBLE_FLIP;
    int LOCAL_SEARCH_LIMIT = 10;
    int GRASP_TIME_LIMIT = 20;
    int OVERALL_TIME_LIMIT = 59;
    double alpha = 0.07;

#ifdef LOG_TO_FILE
    freopen("log_Improvements.out","a+", stdout);
    printf("\n\n\n\n");         // spacing between different logs

    for (int i = 0; i < argc; ++i) {
        printf(argv[i]);
        printf("  ");
    }
    printf("\n\n");
#endif

    if (argc > 1)   {
        for (int i = 1; i < argc - 1; ++i)
            if (!strcmp(argv[i], "-strategy") ) {
                if (!strcmp(argv[i + 1], "FLIP")) {
                    strategy = FLIP;
                } else if (!strcmp(argv[i + 1], "DOUBLE_FLIP")) {
                    strategy = DOUBLE_FLIP;
                } else if (!strcmp(argv[i + 1], "SWAP")) {
                    strategy = SWAP;
                } else if (!strcmp(argv[i + 1], "TRIPLE_FLIP")) {
                    strategy = TRIPLE_FLIP;
                } else if (!strcmp(argv[i + 1], "QUAD_FLIP")) {
                    strategy = QUAD_FLIP;
                } else if (!strcmp(argv[i + 1], "DOUBLE_SWAP")) {
                    strategy = DOUBLE_SWAP;
                } else if (!strcmp(argv[i + 1], "DOUBLE_SWAP_SWAP")) {
                    strategy = DOUBLE_SWAP_SWAP;
                } else if (!strcmp(argv[i + 1], "DOUBLE_FLIP_SWAP")) {
                    strategy = DOUBLE_FLIP_SWAP;
                } else {
                    std::cerr << "Wrong improvement method! Exiting...\n";
                    return 404;
                }
            }
            else if (!strcmp(argv[i], "-first") ) {
                if (!strcmp(argv[i + 1], "true")) {
                    return_after_first_improvement = true;
                }
                else if (!strcmp(argv[i + 1], "false")) {
                    return_after_first_improvement = true;
                }
                else {
                    std::cerr << "Wrong argument on first improvement! Use either 'true' or 'false'\nExiting...\n";
                    return 404;
                }
            }
            else if (!strcmp(argv[i], "-time")) {
                OVERALL_TIME_LIMIT = atoi(argv[i + 1]);
            }
            else if (!strcmp(argv[i], "-localtime")) {
                    LOCAL_SEARCH_LIMIT = atoi(argv[i + 1]);
            }
            else if (!strcmp(argv[i], "-grasptime")) {
                    GRASP_TIME_LIMIT = atoi(argv[i + 1]);
                }
    }


    std::cout << std::setw(13) << "Instance" << std::setw(13) << "Time 1" << std::setw(12) <<
              "1st sol."  << std::setw(15) << "Comp." << std::setw(5) << "Feas"  << std::setw(14) << "Improved sol."
              << std::setw(15) << "Comp."<< std::setw(13) <<
              "Time 2" << std::setw(5) << "Feas" << std::setw(14) << "Relative" << std::endl;

    std::cout << std::setprecision(4) << std::fixed;

    double total_rel_improvement = 0.;
    int total_construction_time = 0;
    int total_improvement_time = 0;
    int total_best_init_sols = 0;
    int total_best_imp_sols = 0;
    double total_comp_improvement = 0.;
    double total_comp_init = 0.;
    int problem = 0;

    for (auto filename: FILES){
        // initialize
        if (readInstance(filename.insert(0,"../Files/"), c, a, b, n, m, q, opt)) {

            std::vector<int> x(n, -1); //solution, -1 by default means not processed by the algorithm

            double time_taken_to_construct = constructionHeuristic(n, m, x, c, a, b);
            total_construction_time += time_taken_to_construct;

            Solution initial_solution;
            for (int i = 0; i < n; ++i)
                initial_solution.set(i, x[i] == 1);

            double localSearchTime;
            Solution improved_solution;


//            std::cout<<filename.substr(9)<<std::endl;
//            for (double alpha = 0.01; alpha <= 0.2; alpha+=0.01){
//                alphaGrasp(n,m,x,c,a,b,alpha,10);
//            }

            int new_objective;
            bool improvement_made = localSearch(n, m, initial_solution, c, a, b, improved_solution, new_objective,
                                                localSearchTime, 10000, strategy, return_after_first_improvement);
            total_improvement_time += localSearchTime;

            initial_solution = improved_solution;
            int init_obj = computeSolutionObjective(n, c, initial_solution);

            double comp_init = 100 * (init_obj - BEST_INIT_SOL_IN_PREV_YEARS[problem]) /
                               (double) BEST_INIT_SOL_IN_PREV_YEARS[problem];
            total_comp_init += comp_init;
            if (comp_init > 0)
                total_best_init_sols++;

            std::cout << std::setw(13) << filename.substr(9) << std::setw(10) << (int) time_taken_to_construct
                      << //solution function
                      " ms" << std::setw(12) << init_obj << std::setw(13) << comp_init << " %" << std::setw(5) <<
                      (checkSolutionFeasibility(n, m, x, a, b) ? "+" : "-");

            localSearchTime = metaheuristic(n, m, improved_solution, c, a, b, strategy, alpha, LOCAL_SEARCH_LIMIT, GRASP_TIME_LIMIT, OVERALL_TIME_LIMIT, return_after_first_improvement);
            int improved_obj = computeSolutionObjective(n, c, improved_solution);
            double improvement_rel = 100 * (improved_obj - init_obj) / (double) init_obj;
            total_rel_improvement += improvement_rel;

            double comp_imp = 100 * (improved_obj - BEST_META_SOL_IN_PREV_YEARS[problem]) /
                              (double) BEST_META_SOL_IN_PREV_YEARS[problem];
            total_comp_improvement += comp_imp;
            if (comp_imp > 0)
                total_best_imp_sols++;
            std::cout << std::setw(14) << improved_obj << std::setw(13) << comp_imp << " %" << std::setw(13)
                      << std::setw(10) << (int) localSearchTime
                      << " ms" << std::setw(5) << (checkSolutionFeasibility(n, m, improved_solution, a, b)
                                                   ? "+" : "-") << std::setw(12) << improvement_rel << " %"
                      << std::endl;

        }
        else
            std::cout<<"Something went wrong! Check file availability!!!";

        problem++;
    }

    printf("\nAverage relative improvement: %8.4f \%\n", total_rel_improvement/FILES.size());
    printf("Total time for construction: %5d ms\n", total_construction_time);
    printf("Total time for improvement:  %5d ms\n", total_improvement_time);

    printf("\nComparison with previous years:\n");
    printf("Best initial solutions:  %5d\tAverage improvement: %14.6f \%\n", total_best_init_sols, total_comp_init/(FILES.size()));
    printf("Best improved solutions: %5d\tAverage improvement: %14.6f \%\n", total_best_imp_sols, total_comp_improvement/(FILES.size()));
    return 0;
}

