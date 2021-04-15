#include <iostream>
#include <fstream>
#include <vector>
#include <limits>
#include <iomanip>
#include <bitset>

const std::vector<std::string> FILES{"100-5-01.txt","100-5-02.txt", "100-5-03.txt", "100-5-04.txt", "100-5-05.txt",
                                     "250-10-01.txt","250-10-02.txt","250-10-03.txt","250-10-04.txt","250-10-05.txt",
                                     "500-30-01.txt","500-30-02.txt","500-30-03.txt","500-30-04.txt","500-30-05.txt"
};

const int MAX_PROBLEM_SIZE = 500;
typedef std::bitset<MAX_PROBLEM_SIZE> Solution;

enum NEIGHBOURHOOD_OPERATOR {
    FLIP,
    DOUBLE_FLIP,
    SWAP
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



bool checkSolutionFeasibilityAfterPerturbing(const int&n, const int&m, const Solution& x,
                                             std::vector<std::vector<int>>& a,
                                             std::vector<int>& b, std::vector<int>& row_activity,
                                             NEIGHBOURHOOD_OPERATOR N_operator, int first, int second = -1)  {

    bool direction = x.test(first);
    bool direction_second = (N_operator == DOUBLE_FLIP) ? x.test(second) : !direction; // if we are swapping, go opposite from the first variable
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
    }

    return true;
}

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

bool yieldNeighbour(const int &n, const int &m,  const Solution& x,
                                                  std::vector<int> &c, std::vector<std::vector<int>>& a,
                                                  std::vector<int>& b, NEIGHBOURHOOD_OPERATOR N_operator,
                                                  Solution& neighbour, int& neighbour_objective,
                                                  bool return_after_first_improvement = false)
{
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
                    if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, FLIP, i)) {
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

        case DOUBLE_FLIP: {

            for (int i = 0; i < n; ++i) {
                int objective_after_first_flip = x.test(i) ? init_objective - c[i] : init_objective + c[i];
                for (int j = 0; j < n; ++j) {
                    if (j == i)
                        continue;
                    if ((current_objective = x.test(j) ? objective_after_first_flip - c[j] :
                                             objective_after_first_flip + c[j]) > neighbour_objective) {
                        if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, DOUBLE_FLIP, i, j)) {
                            neighbour = x;
                            neighbour.flip(i);
                            neighbour.flip(j);
                            neighbour_found = true;
                            neighbour_objective = current_objective;
                            if (return_after_first_improvement)
                                return true;
                        }
                    }
                }
            }
            break;
        }

        case SWAP: {
            for (int i = x._Find_first(); i < n; i = x._Find_next(i)) {           // first is one
                int objective_after_first_flip = init_objective - c[i];
                for (int j = 0; j < n; ++j) {
                    if (j == i || x.test(j))            // second is zero
                        continue;
                    if ((current_objective = objective_after_first_flip + c[j]) > neighbour_objective) {
                        if (checkSolutionFeasibilityAfterPerturbing(n, m, x, a, b, row_activity, SWAP, i, j)) {
                            neighbour = x;
                            neighbour.flip(i);
                            neighbour.flip(j);
                            neighbour_found = true;
                            neighbour_objective = current_objective;
                            if (return_after_first_improvement)
                                return true;
                        }
                    }
                }
            }
            break;

        }
    }



    return neighbour_found;
}


bool localSearch(const int &n, const int &m,  Solution& initial_solution, std::vector<int> &c,
        std::vector<std::vector<int>>& a, std::vector<int>& b, Solution& improved_solution, int& improved_objective,
        double& time_taken, double timeLimit = 3.,
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
        if ((clock() - start) / double(CLOCKS_PER_SEC / 1000) > timeLimit)
            break;
    }


    time_taken = (clock() - start) / double(CLOCKS_PER_SEC / 1000); // time taken by the heuristic in milliseconds

    return improvement_found;
}

int main(int argc, char **argv) {
    std::vector<int> c, b;
    std::vector<std::vector<int>> a;
    int n, m, q, opt;

    std::cout << std::setw(13) << "Instance" << std::setw(13) << "Time 1" << std::setw(17) <<
              "1st sol."  /*<< std::setw(13) << "Check"*/ << std::setw(19) << "Improved sol."<< std::setw(13) <<
              "Time 2" /*<< std::setw(13) << "Check"*/ << std::setw(14) << "Relative" << std::endl;

    std::cout << std::setprecision(4) << std::fixed;

    double total_rel_improvement = 0.;

    for (auto filename: FILES){
        // initialize
        if (readInstance(filename.insert(0,"../Files/"), c, a, b, n, m, q, opt)) {

            std::vector<int> x(n, -1); //solution, -1 by default means not processed by the algorithm

            double time_taken_to_construct = constructionHeuristic(n, m, x, c, a, b);

            Solution initial_solution;
            for (int i = 0; i < n; ++i)
                initial_solution.set(i, x[i] == 1);

            double localSearchTime;
            Solution improved_solution;
            int new_objective;
            bool improvement_made = localSearch(n, m, initial_solution, c, a, b, improved_solution, new_objective,
                                                localSearchTime,60000, DOUBLE_FLIP, false);

            int init_obj = computeSolutionObjective(n, c, initial_solution);

            std::cout << std::setw(13) << filename.substr(9) << std::setw(10) << (int)time_taken_to_construct << //solution function
                      " ms" << std::setw(17) << init_obj /*<< std::setw(13) <<
                      (checkSolutionFeasibility(n,m,x,a,b) ? "feas" : "infeas")*/;
            if (improvement_made) {
                int improved_obj = computeSolutionObjective(n, c, improved_solution);
                double improvement_rel = 100*(improved_obj - init_obj)/(double)init_obj;
                total_rel_improvement += improvement_rel;
                std::cout << std::setw(19) << improved_obj << std::setw(13) << std::setw(10) << (int)localSearchTime
                << " ms" /*<< std::setw(13) <<  (checkSolutionFeasibility(n, m, improved_solution, a, b)
                ? "feas" : "infeas")*/ << std::setw(12) <<  improvement_rel  << " %" << std::endl;
            }
            else    {
                std::cout << "\t\t Improvement not made " << localSearchTime << " ms\n";
            }
        }
        else
            std::cout<<"Something went wrong! Check file availability!!!";
    }

    std::cout << "\nAverage relative improvement: " << total_rel_improvement/FILES.size() << " %" << std::endl;

    return 0;
}

