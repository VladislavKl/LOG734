#include <iostream>
#include <fstream>
#include <vector>
#include <limits>
#include <iomanip>

const std::vector<std::string> FILES{"100-5-01.txt","100-5-02.txt", "100-5-03.txt", "100-5-04.txt", "100-5-05.txt",
                                     "250-10-01.txt","250-10-02.txt","250-10-03.txt","250-10-04.txt","250-10-05.txt",
                                     "500-30-01.txt","500-30-02.txt","500-30-03.txt","500-30-04.txt","500-30-05.txt"
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
                                (double(b[j]) - double(occupied[j]))
                                * (double(b[j]) - double(occupied[j]))
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

int main(int argc, char **argv) {
    std::vector<int> c, b;
    std::vector<std::vector<int>> a;
    int n, m, q, opt;

    for (auto filename: FILES){
        // initialize
        if (readInstance(filename.insert(0,"../Files/"), c, a, b, n, m, q, opt)) {

            std::vector<int> x(n, -1); //solution, -1 by default means not processed by the algorithm

            double time_taken = constructionHeuristic(n, m, x, c, a, b);
            int objFunctionValue = 0; //value of the objective function with variables included by constructionHeuristic
            for (int i = 0; i < n; ++i) {
                objFunctionValue += x[i] * c[i];
            }

            std::cout << filename.substr(9) << "\t"
                      << std::setw(5) << time_taken << //solution function
                      "\tmilliseconds,\t objective function value is" << std:: setw(8) << objFunctionValue
                      << "\t\t" << (checkSolutionFeasibility(n,m,x,a,b) ? "feasible" : "infeasible")
                      << std::endl;
        }
        else
            std::cout<<"Something went wrong! Check file availability!!!";
    }

    return 0;
}

