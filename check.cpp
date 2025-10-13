// crypt_csp_modular.cpp
#include <bits/stdc++.h>
using namespace std;
using ll = long long;

/* ----------------------------- Config toggles ----------------------------- */
/* Flip these to add/remove optimizations */
static const bool USE_AC3 = true;          // run AC-3 domain pruning before search
static const bool USE_WEIGHT_ORDER = true; // order vars by absolute place-weight
static const bool USE_BOUNDS_PRUNE = true; // interval min/max pruning during search
static const bool USE_CARRY_CHECK = true;  // quick column-wise carry consistency check
static const bool STOP_AFTER_FIRST = false;// stop when first solution found
/* -------------------------------------------------------------------------- */

/* ------------------------------ Puzzle types ------------------------------ */
struct Puzzle {
    vector<string> lhs; // addends
    string rhs;
};
/* -------------------------------------------------------------------------- */

/* --------------------------- Parsing / Utilities -------------------------- */
/* trim whitespace */
static inline string trim(const string &s) {
    size_t a = s.find_first_not_of(" \t\r\n");
    if (a == string::npos) return "";
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b-a+1);
}

/* Parse "SEND + MORE = MONEY" style input */
Puzzle parsePuzzle(const string &line) {
    size_t eq = line.find('=');
    if (eq == string::npos) throw runtime_error("Expected '=' in puzzle");
    string left = trim(line.substr(0, eq));
    string right = trim(line.substr(eq+1));
    Puzzle p;
    string token;
    stringstream ss(left);
    while (getline(ss, token, '+')) {
        string w = trim(token);
        if (!w.empty()) p.lhs.push_back(w);
    }
    p.rhs = trim(right);
    return p;
}
/* -------------------------------------------------------------------------- */

/* ------------------------ Letter collection + weights --------------------- */
/* Collect distinct uppercase letters, compute place-weight per letter,
   and mark leading letters (cannot be zero). */
void collectLettersAndWeights(const Puzzle &p,
                              vector<char> &letters,
                              vector<ll> &weight,        // weight per letter (positive for lhs contribution, negative for rhs)
                              vector<bool> &leading)     // true if letter cannot be 0
{
    array<int,26> idx; idx.fill(-1);
    letters.clear();

    auto add = [&](char c){
        if (idx[c-'A'] == -1) {
            idx[c-'A'] = (int)letters.size();
            letters.push_back(c);
        }
    };

    for (auto &w: p.lhs) for (char c: w) if (isalpha(c)) add(c);
    for (char c: p.rhs) if (isalpha(c)) add(c);

    int n = (int)letters.size();
    weight.assign(n, 0);
    leading.assign(n, false);
    for (auto &w: p.lhs) {
        ll place = 1;
        for (int i=(int)w.size()-1;i>=0;--i) {
            weight[idx[w[i]-'A']] += place;
            place *= 10;
        }
        if (w.size()>1) leading[idx[w.front()-'A']] = true;
    }
    {
        ll place = 1;
        for (int i=(int)p.rhs.size()-1;i>=0;--i) {
            weight[idx[p.rhs[i]-'A']] -= place;
            place *= 10;
        }
        if (p.rhs.size()>1) leading[idx[p.rhs.front()-'A']] = true;
    }
}
/* -------------------------------------------------------------------------- */

/* --------------------------- Domain and AC-3 ------------------------------ */
/* Domains: for each variable (letter) we maintain a vector<bool> of allowed digits.
   AC-3 is a generic arc-consistency algorithm; here we encode binary constraint:
   AllDifferent(Xi, Xj) as Xi != Xj. AC-3 will remove values from domains when impossible.
*/

/* Helper: check if Xi value has any support in Xj domain for constraint Xi != Xj */
bool hasSupportNotEqual(const array<bool,10> &domXj, int val) {
    // any value in domXj different from val
    for (int d=0; d<=9; ++d) if (domXj[d] && d != val) return true;
    return false;
}

/* /* Run AC-3 over AllDifferent binary arcs to reduce domains.
      domains: vector<array<bool,10>> for each var.
      letters count must be <= 10 (otherwise impossible).
      This is optional optimization; safe to skip if you want simpler solver. */
bool ac3_all_diff(vector<array<bool,10>> &domains) {
    int n = domains.size();
    deque<pair<int,int>> q;
    for (int i=0;i<n;++i) for (int j=0;j<n;++j) if (i!=j) q.emplace_back(i,j);

    while (!q.empty()) {
        auto [xi,xj] = q.front(); q.pop_front();
        // For every value a in dom(xi), must exist b in dom(xj) such that a!=b.
        bool revised = false;
        for (int a=0;a<=9;++a) {
            if (!domains[xi][a]) continue;
            if (!hasSupportNotEqual(domains[xj], a)) {
                domains[xi][a] = false;
                revised = true;
            }
        }
        if (revised) {
            // if domain emptied -> inconsistent
            bool empty=true;
            for (int d=0; d<=9; ++d) if (domains[xi][d]) { empty=false; break; }
            if (empty) return false;
            // enqueue all neighbors (xk, xi)
            for (int k=0;k<n;++k) if (k!=xi && k!=xj) q.emplace_back(k, xi);
        }
    }
    return true;
}
/* -------------------------------------------------------------------------- */

/* ---------------------- Variable ordering helpers ------------------------- */
/* Create an ordering of variables to assign.
   - If USE_WEIGHT_ORDER=true, sort by absolute weight descending (more impact first).
   - Otherwise use simple index order. */
vector<int> makeVariableOrder(const vector<ll> &weight) {
    int n = weight.size();
    vector<int> order(n);
    iota(order.begin(), order.end(), 0);
    if (USE_WEIGHT_ORDER) {
        sort(order.begin(), order.end(), [&](int a, int b){
            if (llabs(weight[a]) != llabs(weight[b])) return llabs(weight[a]) > llabs(weight[b]);
            return a < b;
        });
    }
    return order;
}
/* -------------------------------------------------------------------------- */

/* ------------------------- Bounds pruning (relaxation) -------------------- */
/* Compute optimistic min/max for sum of words given current assignments and remaining digits.
   This relaxation ignores AllDifferent among unassigned (optimistic), but respects leading-zero rule.
   Used to prune branches where LHS interval cannot meet RHS interval. */

// Corrected function
pair<ll,ll> wordMinMaxRelaxed(const string &w,
                              const vector<int> &assign,
                              const vector<int> &letterIndex,
                              const vector<bool> &leading,
                              const array<bool,10> &usedDigits)
{
    vector<int> freeDigits;
    for (int d=0; d<=9; ++d) if (!usedDigits[d]) freeDigits.push_back(d);

    ll mn = 0, mx = 0;
    
    // Pointers for consuming free digits for min and max bounds
    int min_ptr = 0;
    int max_ptr = (int)freeDigits.size() - 1;

    // We must iterate from left-to-right (most-significant to least-significant)
    for (size_t i = 0; i < w.size(); ++i) {
        mn *= 10;
        mx *= 10;

        int var = letterIndex[w[i]-'A'];
        int val = assign[var];

        if (val != -1) {
            mn += val;
            mx += val;
        } else {
            // --- MIN value: assign smallest available digits ---
            int digit_for_min;
            // Handle leading zero constraint for the minimum bound
            if (i == 0 && w.size() > 1 && freeDigits[min_ptr] == 0) {
                // If this is a leading position and the smallest free digit is 0,
                // we must use the next smallest one.
                if (min_ptr + 1 < freeDigits.size()) {
                    digit_for_min = freeDigits[min_ptr + 1];
                    // We effectively "use" the next digit, but for subsequent places,
                    // the original smallest (0) is still available. For simplicity in this
                    // relaxation, we'll just advance the pointer. A more complex swap
                    // could provide a slightly tighter bound but this is correct.
                    // To keep it simple and correct, we just use the digit but advance
                    // the main pointer for the next unassigned variable.
                } else {
                    // This implies only 0 is available for a leading digit, an impossible state
                    // that will be pruned correctly by the main solver's leading-zero check.
                    digit_for_min = 0;
                }
            } else {
                digit_for_min = freeDigits[min_ptr];
            }
            mn += digit_for_min;
            min_ptr++;

            // --- MAX value: assign largest available digits ---
            mx += freeDigits[max_ptr];
            max_ptr--;
        }
    }
    return {mn, mx};
}

/* Compute LHS and RHS min/max relaxed sums */
void computeTotalRangesRelaxed(const Puzzle &p,
                               const vector<int> &assign,
                               const vector<int> &letterIndex,
                               const vector<bool> &leading,
                               const array<bool,10> &usedDigits,
                               pair<ll,ll> &lhsRange,
                               pair<ll,ll> &rhsRange)
{
    ll lmin=0, lmax=0;
    for (auto &w: p.lhs) {
        auto pr = wordMinMaxRelaxed(w, assign, letterIndex, leading, usedDigits);
        lmin += pr.first; lmax += pr.second;
    }
    auto prr = wordMinMaxRelaxed(p.rhs, assign, letterIndex, leading, usedDigits);
    lhsRange = {lmin, lmax};
    rhsRange = prr;
}
/* -------------------------------------------------------------------------- */

/* ------------------------ Column carry quick check ------------------------ */
/* Quick column-wise check: with current partial assignment try to see if
   there exists possible carries that can make column equations feasible.
   This is a light, local prune; conservative (if unsure, do not prune). */

bool quickColumnCheck(const Puzzle &p,
                      const vector<int> &assign,
                      const vector<int> &letterIndex,
                      const vector<bool> &leading,
                      const array<bool,10> &usedDigits)
{
    int numCols = max( (int)p.rhs.size(), (int) (p.lhs.empty()?0:p.lhs[0].size()) );
    // simpler: check from least significant column to most, ensure intervals of sums mod10 possible with carry bounds
    int maxCols = max((int)p.rhs.size(), 0);
    int maxLen = 0;
    for (auto &w: p.lhs) maxLen = max(maxLen, (int)w.size());
    maxCols = max(maxCols, maxLen);

    int carryLow = 0, carryHigh = 0; // possible carry into current column
    for (int col=0; col<maxCols; ++col) {
        // compute min and max possible sum of digits in this column
        int colMin = 0, colMax = 0;
        // LHS digits in this column
        for (auto &w: p.lhs) {
            int pos = (int)w.size() - 1 - col;
            if (pos < 0) continue;
            int var = letterIndex[w[pos]-'A'];
            if (assign[var] != -1) { colMin += assign[var]; colMax += assign[var]; }
            else {
                // unassigned: smallest possible digit respecting leading
                int mn = 9, mx = 0;
                for (int d=0; d<=9; ++d) if (!usedDigits[d]) {
                    if (pos==0 && w.size()>1 && d==0) continue;
                    mn = min(mn, d); mx = max(mx, d);
                }
                if (mn==9 && mx==0) { /* no free digits, but may be assigned elsewhere */ mn = 0; mx = 9; }
                colMin += mn; colMax += mx;
            }
        }
        // RHS digit for this column
        int posR = (int)p.rhs.size() - 1 - col;
        if (posR < 0) {
            // if RHS doesn't have digit but LHS has non-zero min with carry, impossible
            if (colMin + carryLow > carryHigh + 0 && colMin + carryLow > 0) {
                // still not decisive; skip deep pruning
            }
        } else {
            int varR = letterIndex[p.rhs[posR]-'A'];
            int rmin, rmax;
            if (assign[varR] != -1) rmin = rmax = assign[varR];
            else {
                rmin = 9; rmax = 0;
                for (int d=0; d<=9; ++d) if (!usedDigits[d]) {
                    if (posR==0 && p.rhs.size()>1 && d==0) continue;
                    rmin = min(rmin, d); rmax = max(rmax, d);
                }
                if (rmin==9 && rmax==0) { rmin = 0; rmax = 9; }
            }
            // feasible sums s = LHS_sum + carryIn should satisfy (s % 10) in [rmin,rmax] and carryOut appropriate
            int possible = 0;
            // We coarsely check if intervals overlap modulo 10 by scanning carry values 0..(number of addends)
            int addCount = p.lhs.size();
            int maxCarryPossible = addCount; // upper bound for carry into next column
            for (int cin = carryLow; cin <= carryHigh + 1; ++cin) {
                int smin = colMin + cin;
                int smax = colMax + cin;
                // see if there exists some s in [smin,smax] with s%10 in [rmin,rmax]
                for (int t = smin; t <= smax; ++t) {
                    int digit = t % 10;
                    if (digit < 0) digit += 10;
                    if (digit >= rmin && digit <= rmax) { possible = 1; break; }
                }
                if (possible) break;
            }
            if (!possible) return false;
            // update carry bounds conservatively
            // carryOut in [ (colMin + carryLow) / 10 , (colMax + carryHigh) / 10 ]
            int newCarryLow = (colMin + carryLow) / 10;
            int newCarryHigh = (colMax + carryHigh) / 10;
            carryLow = newCarryLow; carryHigh = newCarryHigh;
            if (carryLow > carryHigh) return false;
        }
    }
    return true;
}
/* -------------------------------------------------------------------------- */

/* --------------------------- Backtracking search -------------------------- */
/* Main recursive search. assign[var] = digit or -1. usedDigits tracks digits.
   order[] defines variable assignment order. Solutions appended to vector.
*/
void backtrackSolve(const Puzzle &p,
                    const vector<char> &letters,
                    const vector<int> &letterIndexMap, // size 26: -1 or var idx
                    const vector<int> &order,
                    const vector<bool> &leading,
                    vector<int> &assign,
                    array<bool,10> &usedDigits,
                    vector<vector<int>> &solutions)
{
    int n = letters.size();
    // find next unassigned by order
    int nextPos = -1;
    for (int i=0;i<n;++i) if (assign[ order[i] ] == -1) { nextPos = order[i]; break; }
    if (nextPos == -1) {
        // full assignment -> verify equation
        auto evalWord = [&](const string &w)->ll{
            ll v=0;
            for (char c: w) v = v*10 + assign[ letterIndexMap[c-'A'] ];
            return v;
        };
        ll L=0; for (auto &w: p.lhs) L += evalWord(w);
        ll R = evalWord(p.rhs);
        if (L == R) {
            solutions.emplace_back(assign);
            if (STOP_AFTER_FIRST) return;
        }
        return;
    }
    // candidate digits
    for (int d=0; d<=9; ++d) {
        if (usedDigits[d]) continue;
        if (leading[nextPos] && d==0) continue;
        // assign
        assign[nextPos] = d; usedDigits[d] = true;

        bool ok = true;
        // Optional pruning: bounds relaxed
        if (USE_BOUNDS_PRUNE) {
            pair<ll,ll> lhsRange, rhsRange;
            computeTotalRangesRelaxed(p, assign, letterIndexMap, leading, usedDigits, lhsRange, rhsRange);
            if (lhsRange.second < rhsRange.first || lhsRange.first > rhsRange.second) ok = false;
        }
        // Optional quick carry check
        if (ok && USE_CARRY_CHECK) {
            if (!quickColumnCheck(p, assign, letterIndexMap, leading, usedDigits)) ok = false;
        }

        if (ok) {
            backtrackSolve(p, letters, letterIndexMap, order, leading, assign, usedDigits, solutions);
            if (STOP_AFTER_FIRST && !solutions.empty()) return;
        }
        // undo
        assign[nextPos] = -1; usedDigits[d] = false;
    }
}
/* -------------------------------------------------------------------------- */

/* ----------------------------- Public API -------------------------------- */
/* findSolutions: orchestrates everything, exposing toggles implicitly */
vector<vector<int>> findSolutions(const Puzzle &p) {
    vector<char> letters;
    vector<ll> weight;
    vector<bool> leading;
    collectLettersAndWeights(p, letters, weight, leading);
    int n = letters.size();
    if (n > 10) {
        cerr << "More than 10 distinct letters -> impossible.\n";
        return {};
    }

    // map char->index
    vector<int> letterIndexMap(26, -1);
    for (int i=0;i<n;++i) letterIndexMap[ letters[i]-'A' ] = i;

    // domains init: either full 0..9 or with leading constraint removed
    vector<array<bool,10>> domains(n);
    for (int i=0;i<n;++i) {
        for (int d=0; d<=9; ++d) domains[i][d] = true;
        if (leading[i]) domains[i][0] = false;
    }

    // Optional AC-3
    if (USE_AC3) {
        bool ac3_ok = ac3_all_diff(domains);
        if (!ac3_ok) return {};
    }

    // initial assignment & used digits
    vector<int> assign(n, -1);
    array<bool,10> usedDigits; usedDigits.fill(false);

    // If AC3 run, we could optionally try to preassign singleton domains (simple forward-checking)
    for (int i=0;i<n;++i) {
        int cnt=0,val=-1;
        for (int d=0; d<=9; ++d) if (domains[i][d]) { cnt++; val=d; }
        if (cnt==1) { assign[i]=val; usedDigits[val]=true; }
    }

    vector<int> order = makeVariableOrder(weight);

    // if some preassigned, ensure order puts unassigned first
    // (but makeVariableOrder already returns static order; backtrack solves by checking assign==-1)

    vector<vector<int>> solutions;
    backtrackSolve(p, letters, letterIndexMap, order, leading, assign, usedDigits, solutions);
    return solutions;
}
/* -------------------------------------------------------------------------- */

/* ----------------------------- Printing utils ---------------------------- */
void printSolution(const Puzzle &p, const vector<int> &sol, const vector<char> &letters) {
    // map char->digit
    unordered_map<char,int> m;
    for (int i=0;i<(int)letters.size();++i) m[letters[i]] = sol[i];
    auto eval = [&](const string &w)->ll{
        ll v=0;
        for (char c: w) v = v*10 + m[c];
        return v;
    };
    for (int i=0;i<(int)letters.size();++i) cout << letters[i] << '=' << sol[i] << ' ';
    cout << '\n';
    ll L=0;
    for (auto &w: p.lhs) { cout << w << '(' << eval(w) << ") + "; L += eval(w); }
    cout << "\b\b= " << p.rhs << '(' << eval(p.rhs) << ')' << '\n';
    cout << "Check: " << L << " == " << eval(p.rhs) << "\n\n";
}
/* -------------------------------------------------------------------------- */

/* ---------------------------------- main --------------------------------- */
int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    // Edit this puzzle or read from stdin
    string puzzleLine = "SEND + MORE = MONEY";
    // or uncomment to read from stdin:
    // getline(cin, puzzleLine);

    Puzzle p = parsePuzzle(puzzleLine);

    vector<char> letters;
    vector<ll> weight;
    vector<bool> leading;
    collectLettersAndWeights(p, letters, weight, leading);

    cout << "Puzzle: " << puzzleLine << "\n";
    cout << "Distinct letters (" << letters.size() << "): ";
    for (char c: letters) cout << c << ' ';
    cout << "\n";
    cout << "Using optimizations: AC-3=" << USE_AC3 << " WeightOrder=" << USE_WEIGHT_ORDER
         << " BoundsPrune=" << USE_BOUNDS_PRUNE << " CarryCheck=" << USE_CARRY_CHECK << "\n\n";

    auto sols = findSolutions(p);
    if (sols.empty()) {
        cout << "No solutions found.\n";
        return 0;
    }
    cout << "Solutions found: " << sols.size() << "\n\n";
    for (auto &sol : sols) printSolution(p, sol, letters);
    return 0;
}
