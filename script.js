// script.js

// --- Global State for Visualization ---
let visualizationStates = [];
let currentStep = -1;
let allSolutions = [];

// --- Config Toggles (Mirroring C++ static consts) ---
let config = {
    USE_AC3: true,
    USE_WEIGHT_ORDER: true,
    USE_BOUNDS_PRUNE: true,
    USE_CARRY_CHECK: true,
    STOP_AFTER_FIRST: false
};

// --- DOM Elements ---
const puzzleInput = document.getElementById('puzzleInput');
const solveBtn = document.getElementById('solveBtn');
const resetBtn = document.getElementById('resetBtn');
const puzzleDisplay = document.getElementById('puzzleDisplay');
const assignmentDisplay = document.getElementById('assignmentDisplay');
const domainsGrid = document.getElementById('domainsGrid');
const stepExplanation = document.getElementById('stepExplanation');
const solutionsList = document.getElementById('solutionsList');
const prevStepBtn = document.getElementById('prevStepBtn');
const nextStepBtn = document.getElementById('nextStepBtn');
const lastStepBtn = document.getElementById('lastStepBtn');

// Optimization toggles
const toggleAC3 = document.getElementById('toggleAC3');
const toggleWeightOrder = document.getElementById('toggleWeightOrder');
const toggleBoundsPrune = document.getElementById('toggleBoundsPrune');
const toggleCarryCheck = document.getElementById('toggleCarryCheck');
const toggleStopAfterFirst = document.getElementById('toggleStopAfterFirst');

// --- Helper Data Structures (JavaScript equivalents of C++ ones) ---
class Puzzle {
    constructor(lhs, rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

// Global variables that will be populated after parsing the puzzle
let letters = []; // ['S', 'E', 'N', 'D', 'M', 'O', 'R', 'Y']
let letterIndexMap = new Map(); // {'S': 0, 'E': 1, ...}
let weights = []; // Impact weight for each letter
let leadingLetters = []; // [true, false, ...] indicating if letter cannot be 0

// --- Visualization State Capture Function ---
function captureState(explanation, highlightedVar = null, highlightedDigit = null, prunedInfo = null, success = false, failure = false) {
    const currentAssignments = new Map();
    for (let i = 0; i < letters.length; i++) {
        currentAssignments.set(letters[i], backtrackAssignments[i]);
    }

    const currentDomains = new Map();
    for (let i = 0; i < letters.length; i++) {
        const domainDigits = [];
        for (let d = 0; d <= 9; d++) {
            if (backtrackDomains[i][d]) {
                domainDigits.push(d);
            }
        }
        currentDomains.set(letters[i], domainDigits);
    }

    visualizationStates.push({
        assignments: currentAssignments, // Map<char, digit | -1>
        domains: currentDomains,         // Map<char, Array<digit>>
        explanation: explanation,
        highlightedVar: highlightedVar,  // char, e.g., 'S'
        highlightedDigit: highlightedDigit, // digit, e.g., 9
        prunedInfo: prunedInfo,          // { var: 'X', digit: D } or { var: 'X', digit: [D1, D2] } for multiple prunes
        success: success,
        failure: failure
    });
}


// --- Core CSP Solver Logic (Ported from C++ and instrumented) ---

// Globals used during backtracking
let backtrackAssignments = []; // [digit | -1, ...] corresponds to letters array
let backtrackUsedDigits = new Array(10).fill(false); // [true/false for digit 0-9]
let backtrackDomains = []; // Array of Array<bool> for each letter's domain

function parsePuzzle(line) {
    const parts = line.split('=');
    const lhsStr = parts[0].trim();
    const rhsStr = parts[1].trim();

    const lhsWords = lhsStr.split('+').map(w => w.trim()).filter(w => w.length > 0);
    return new Puzzle(lhsWords, rhsStr);
}

function collectLettersAndWeights(puzzle) {
    const distinctLetters = new Set();
    for (const w of puzzle.lhs) {
        for (const char of w) distinctLetters.add(char);
    }
    for (const char of puzzle.rhs) distinctLetters.add(char);

    letters = Array.from(distinctLetters).sort(); // Keep consistent order
    letterIndexMap = new Map();
    for (let i = 0; i < letters.length; i++) {
        letterIndexMap.set(letters[i], i);
    }

    weights = new Array(letters.length).fill(0);
    leadingLetters = new Array(letters.length).fill(false);

    for (const w of puzzle.lhs) {
        let place = 1;
        for (let i = w.length - 1; i >= 0; --i) {
            weights[letterIndexMap.get(w[i])] += place;
            place *= 10;
        }
        if (w.length > 1) leadingLetters[letterIndexMap.get(w[0])] = true;
    }
    let place = 1;
    for (let i = puzzle.rhs.length - 1; i >= 0; --i) {
        weights[letterIndexMap.get(puzzle.rhs[i])] -= place;
        place *= 10;
    }
    if (puzzle.rhs.length > 1) leadingLetters[letterIndexMap.get(puzzle.rhs[0])] = true;
}

// Helper: check if Xi value has any support in Xj domain for constraint Xi != Xj
function hasSupportNotEqual(domXj, val) {
    for (let d = 0; d <= 9; ++d) {
        if (domXj[d] && d !== val) return true;
    }
    return false;
}

function ac3_all_diff(domains) {
    if (!config.USE_AC3) return true;

    const n = domains.length;
    const q = []; // Using an array as a deque
    for (let i = 0; i < n; ++i) {
        for (let j = 0; j < n; ++j) {
            if (i !== j) q.push([i, j]);
        }
    }

    let initialDomainsState = domains.map(d => [...d]); // Deep copy for comparison

    while (q.length > 0) {
        const [xi, xj] = q.shift();
        let revised = false;
        let removedDigits = [];

        for (let a = 0; a <= 9; ++a) {
            if (!domains[xi][a]) continue; // Already removed
            if (!hasSupportNotEqual(domains[xj], a)) {
                domains[xi][a] = false;
                revised = true;
                removedDigits.push(a);
            }
        }

        if (revised) {
            if (removedDigits.length > 0) {
                 captureState(`AC-3 pruned ${removedDigits.join(',')} from domain of ${letters[xi]} because of ${letters[xj]}.`,
                              letters[xi], null, {var: letters[xi], digits: removedDigits});
            }

            // if domain emptied -> inconsistent
            let empty = true;
            for (let d = 0; d <= 9; ++d) if (domains[xi][d]) { empty = false; break; }
            if (empty) {
                captureState(`AC-3: Domain of ${letters[xi]} became empty, inconsistent.`, letters[xi], null, null, false, true);
                return false; // Inconsistent
            }
            // enqueue all neighbors (xk, xi)
            for (let k = 0; k < n; ++k) {
                if (k !== xi && k !== xj) q.push([k, xi]);
            }
        }
    }
    return true;
}

function makeVariableOrder(puzzleLetters, letterWeights) {
    const n = puzzleLetters.length;
    const order = Array.from({ length: n }, (_, i) => i); // [0, 1, 2, ...]

    if (config.USE_WEIGHT_ORDER) {
        order.sort((a, b) => {
            const absWeightA = Math.abs(letterWeights[a]);
            const absWeightB = Math.abs(letterWeights[b]);
            if (absWeightA !== absWeightB) {
                return absWeightB - absWeightA; // Descending by abs weight
            }
            return a - b; // Tie-break by original index
        });
    }
    return order; // Array of indices
}


// Corrected wordMinMaxRelaxed (JS version of the C++ corrected function)
function wordMinMaxRelaxed(word, assignArr, lIndexMap, leadingArr, usedDigitsArr) {
    const freeDigits = [];
    for (let d = 0; d <= 9; ++d) {
        if (!usedDigitsArr[d]) {
            freeDigits.push(d);
        }
    }

    let mn = 0;
    let mx = 0;

    let min_ptr = 0;
    let max_ptr = freeDigits.length - 1;

    for (let i = 0; i < word.length; ++i) {
        mn *= 10;
        mx *= 10;

        const char = word[i];
        const varIdx = lIndexMap.get(char);
        const val = assignArr[varIdx];

        if (val !== -1) {
            mn += val;
            mx += val;
        } else {
            // --- MIN value ---
            let digit_for_min;
            if (i === 0 && word.length > 1 && freeDigits[min_ptr] === 0) {
                if (min_ptr + 1 < freeDigits.length) {
                    digit_for_min = freeDigits[min_ptr + 1];
                } else {
                    digit_for_min = 0; // Fallback, should ideally be pruned earlier
                }
            } else {
                digit_for_min = freeDigits[min_ptr];
            }
            mn += digit_for_min;
            min_ptr++;

            // --- MAX value ---
            mx += freeDigits[max_ptr];
            max_ptr--;
        }
    }
    return { min: mn, max: mx };
}

function computeTotalRangesRelaxed(puzzle, assignArr, lIndexMap, leadingArr, usedDigitsArr) {
    let lhsMin = 0, lhsMax = 0;
    for (const w of puzzle.lhs) {
        const { min, max } = wordMinMaxRelaxed(w, assignArr, lIndexMap, leadingArr, usedDigitsArr);
        lhsMin += min;
        lhsMax += max;
    }
    const rhsRange = wordMinMaxRelaxed(puzzle.rhs, assignArr, lIndexMap, leadingArr, usedDigitsArr);
    return { lhs: { min: lhsMin, max: lhsMax }, rhs: rhsRange };
}

// Corrected quickColumnCheck (JS version of the C++ corrected function)
function quickColumnCheck(puzzle, assignArr, lIndexMap, leadingArr, usedDigitsArr) {
    if (!config.USE_CARRY_CHECK) return true;

    let maxCols = puzzle.rhs.length;
    for (const w of puzzle.lhs) {
        maxCols = Math.max(maxCols, w.length);
    }

    let carryLow = 0;
    let carryHigh = 0;

    for (let col = 0; col < maxCols; ++col) {
        let colMin = 0;
        let colMax = 0;

        // LHS digits
        for (const w of puzzle.lhs) {
            const pos = w.length - 1 - col;
            if (pos < 0) continue;
            const varIdx = lIndexMap.get(w[pos]);
            if (assignArr[varIdx] !== -1) {
                colMin += assignArr[varIdx];
                colMax += assignArr[varIdx];
            } else {
                // Find min/max *free* digits for this position
                let minFree = 9, maxFree = 0;
                let foundFree = false;
                for (let d = 0; d <= 9; ++d) {
                    if (!usedDigitsArr[d]) {
                        // Leading zero check
                        if (pos === 0 && w.length > 1 && d === 0) continue;
                        minFree = Math.min(minFree, d);
                        maxFree = Math.max(maxFree, d);
                        foundFree = true;
                    }
                }
                // If no free digits left for this var, it must be assigned already by AC3/forward checking
                // If it's -1, this implies a bug or we need to consider it can take any digit (0-9)
                // for the purpose of this *relaxation* if its domain is not empty, but we've used usedDigitsArr
                // so it means "any *currently unused* digit"
                if (!foundFree) { minFree = 0; maxFree = 9; } // Fallback if no specific free digit found
                colMin += minFree;
                colMax += maxFree;
            }
        }

        // RHS digit
        const posR = puzzle.rhs.length - 1 - col;
        let rmin, rmax;

        if (posR < 0) {
            // No RHS digit for this column, implies LHS sum must eventually become 0
            // and carry must balance out. This check is more complex.
            // For simplicity here, we'll return true, as this check is a light prune.
            // A more rigorous check would ensure colMin + carryLow <= carryHigh * 10 (roughly)
            // if (colMin + carryLow > 0 && colMin + carryLow > carryHigh * 10) return false;
            // For now, if RHS ends, we assume carry can propagate correctly.
        } else {
            const varRIdx = lIndexMap.get(puzzle.rhs[posR]);
            if (assignArr[varRIdx] !== -1) {
                rmin = rmax = assignArr[varRIdx];
            } else {
                let minFree = 9, maxFree = 0;
                let foundFree = false;
                for (let d = 0; d <= 9; ++d) {
                    if (!usedDigitsArr[d]) {
                        if (posR === 0 && puzzle.rhs.length > 1 && d === 0) continue;
                        minFree = Math.min(minFree, d);
                        maxFree = Math.max(maxFree, d);
                        foundFree = true;
                    }
                }
                if (!foundFree) { minFree = 0; maxFree = 9; }
                rmin = minFree;
                rmax = maxFree;
            }

            let possible = false;
            const addCount = puzzle.lhs.length; // max number of summands
            const maxCarryPossible = addCount; // rough upper bound for carry-in for next col sum
            
            // Loop through possible incoming carries and check if any sums are feasible
            for (let cin = carryLow; cin <= carryHigh + maxCarryPossible; ++cin) { // Increased upper bound for cin for safety
                let smin = colMin + cin;
                let smax = colMax + cin;

                // Check for overlap of (s % 10) with [rmin, rmax]
                for (let t = smin; t <= smax; ++t) {
                    const digit = t % 10;
                    if (digit >= rmin && digit <= rmax) {
                        possible = true;
                        break;
                    }
                }
                if (possible) break;
            }
            if (!possible) return false;

            // Update carry bounds for next column
            const newCarryLow = Math.floor((colMin + carryLow) / 10);
            // Corrected: (colMax + carryHigh) / 10, not (colMax + carryHigh + 9) / 10
            const newCarryHigh = Math.floor((colMax + carryHigh) / 10);

            carryLow = newCarryLow;
            carryHigh = newCarryHigh;

            if (carryLow > carryHigh) return false;
        }
    }
    // Final check for overall carry
    if (carryLow !== 0 || carryHigh !== 0) {
        // If RHS is shorter than LHS, final carry must be 0 for a solution
        // A more rigorous check would be needed here. For now, lenient.
    }
    return true;
}


// Backtracking Search (Recursive)
function backtrackSolve(puzzle, orderIdx = 0) {
    const n = letters.length;

    // Find next unassigned variable in the chosen order
    let nextVarIdx = -1;
    for (let i = 0; i < n; ++i) {
        const currentOrderedVarIdx = order[i];
        if (backtrackAssignments[currentOrderedVarIdx] === -1) {
            nextVarIdx = currentOrderedVarIdx;
            break;
        }
    }

    if (nextVarIdx === -1) {
        // Full assignment, verify equation
        const evalWord = (word) => {
            let val = 0;
            for (const char of word) {
                val = val * 10 + backtrackAssignments[letterIndexMap.get(char)];
            }
            return val;
        };

        let lhsSum = 0;
        for (const w of puzzle.lhs) {
            lhsSum += evalWord(w);
        }
        const rhsVal = evalWord(puzzle.rhs);

        if (lhsSum === rhsVal) {
            const solutionMap = new Map();
            for (let i = 0; i < n; i++) {
                solutionMap.set(letters[i], backtrackAssignments[i]);
            }
            allSolutions.push(solutionMap);
            captureState(`Solution found! ${lhsSum} = ${rhsVal}`, null, null, null, true);
            return config.STOP_AFTER_FIRST ? true : false; // Found a solution, stop if configured
        } else {
            captureState(`Full assignment tried but ${lhsSum} !== ${rhsVal}. Backtracking.`, null, null, null, false, true);
        }
        return false; // Not a solution or continue search
    }

    const nextVarChar = letters[nextVarIdx];
    captureState(`Trying to assign ${nextVarChar}.`, nextVarChar);

    // Try candidate digits for nextVarIdx
    // Iterate over the current domain for this variable, if AC3 was run
    const possibleDigits = [];
    for(let d=0; d<=9; ++d) {
        if (backtrackDomains[nextVarIdx][d]) { // Use the pruned domain
            possibleDigits.push(d);
        }
    }

    for (const d of possibleDigits) {
        if (backtrackUsedDigits[d]) {
            captureState(`Digit ${d} is already used. Skipping for ${nextVarChar}.`, nextVarChar, d);
            continue;
        }
        if (leadingLetters[nextVarIdx] && d === 0) {
            captureState(`${nextVarChar} cannot be 0 (leading letter). Skipping digit 0.`, nextVarChar, d);
            continue;
        }

        // Assign
        backtrackAssignments[nextVarIdx] = d;
        backtrackUsedDigits[d] = true;
        captureState(`Assigned ${nextVarChar}=${d}.`, nextVarChar, d);

        let ok = true;

        // Optional Pruning: Bounds Relaxed
        if (config.USE_BOUNDS_PRUNE) {
            const { lhs, rhs } = computeTotalRangesRelaxed(puzzle, backtrackAssignments, letterIndexMap, leadingLetters, backtrackUsedDigits);
            if (lhs.max < rhs.min || lhs.min > rhs.max) {
                captureState(`Bounds pruning: LHS range [${lhs.min}, ${lhs.max}] does not overlap with RHS range [${rhs.min}, ${rhs.max}]. Pruning branch.`, nextVarChar, d, null, false, true);
                ok = false;
            } else {
                captureState(`Bounds check passed for ${nextVarChar}=${d}. LHS range [${lhs.min}, ${lhs.max}], RHS range [${rhs.min}, ${rhs.max}].`, nextVarChar, d);
            }
        }

        // Optional Quick Carry Check
        if (ok && config.USE_CARRY_CHECK) {
            if (!quickColumnCheck(puzzle, backtrackAssignments, letterIndexMap, leadingLetters, backtrackUsedDigits)) {
                captureState(`Carry check failed for ${nextVarChar}=${d}. Pruning branch.`, nextVarChar, d, null, false, true);
                ok = false;
            } else {
                captureState(`Carry check passed for ${nextVarChar}=${d}.`, nextVarChar, d);
            }
        }
        
        // Recursive call
        if (ok) {
            if (backtrackSolve(puzzle, orderIdx + 1) && config.STOP_AFTER_FIRST) {
                return true;
            }
        }

        // Undo assignment (backtrack)
        backtrackAssignments[nextVarIdx] = -1;
        backtrackUsedDigits[d] = false;
        captureState(`Backtracking: Unassigned ${nextVarChar}.`, nextVarChar, d);
    }
    return false;
}

// Main solver function (findSolutions equivalent)
let puzzleInstance = null;
let order = []; // Store the variable order

// script.js

// Replace the existing findSolutionsWrapper function with this one.

function findSolutionsWrapper() {
    visualizationStates = [];
    currentStep = -1;
    allSolutions = [];

    const puzzleLine = puzzleInput.value;
    try {
        puzzleInstance = parsePuzzle(puzzleLine);
    } catch (e) {
        stepExplanation.textContent = `Error parsing puzzle: ${e.message}`;
        return;
    }

    collectLettersAndWeights(puzzleInstance);

    const n = letters.length;
    if (n > 10) {
        stepExplanation.textContent = "More than 10 distinct letters -> impossible.";
        return;
    }

    // Initialize domains for backtracking
    backtrackDomains = Array.from({ length: n }, () => new Array(10).fill(true));
    for (let i = 0; i < n; ++i) {
        if (leadingLetters[i]) backtrackDomains[i][0] = false;
    }
    captureState("Initial state: Domains set, leading zeros restricted.");

    // Run AC-3
    const ac3_ok = ac3_all_diff(backtrackDomains);
    if (!ac3_ok) {
        renderState(visualizationStates.length - 1);
        return;
    } else {
        captureState("AC-3 completed domain pruning.");
    }
    
    // Initial assignment & used digits
    backtrackAssignments = new Array(n).fill(-1);
    backtrackUsedDigits.fill(false);

    // Preassign singleton domains from AC-3
    let preassignedCount = 0;
    for (let i = 0; i < n; ++i) {
        const domainDigits = [];
        for (let d = 0; d <= 9; ++d) {
            if (backtrackDomains[i][d]) domainDigits.push(d);
        }
        if (domainDigits.length === 1) {
            const val = domainDigits[0];
            backtrackAssignments[i] = val;
            backtrackUsedDigits[val] = true;
            preassignedCount++;
            captureState(`Pre-assigned ${letters[i]}=${val} (singleton domain from AC-3).`, letters[i], val);
        }
    }
    if (preassignedCount > 0) {
        captureState(`${preassignedCount} variables pre-assigned from singleton domains.`);
    }

    order = makeVariableOrder(letters, weights);
    captureState(`Variable order determined: ${order.map(idx => letters[idx]).join(', ')}. Starting backtracking.`);
    
    // --- Start the recursive search ---
    backtrackSolve(puzzleInstance); 

    // --- Process results and add a final summary state ---
    if (allSolutions.length === 0) {
        solutionsList.textContent = "No solutions found.";
        // Add a final state showing the end result
        const finalAssignments = new Map();
        letters.forEach(l => finalAssignments.set(l, -1));

        visualizationStates.push({
            assignments: finalAssignments,
            domains: new Map(), // Domains don't matter in the final state
            explanation: "Search completed. No solutions were found.",
            highlightedVar: null,
            highlightedDigit: null,
            prunedInfo: null,
            success: false,
            failure: true
        });

    } else {
        let solutionsText = `Found ${allSolutions.length} solution(s):\n`;
        allSolutions.forEach(sol => {
            let line = "";
            for (const [char, digit] of sol.entries()) line += `${char}=${digit} `;
            line += "\n";
            let lhsEval = 0;
            let equationPart = "";
            puzzleInstance.lhs.forEach(word => {
                let wordValStr = "";
                for (const char of word) wordValStr += sol.get(char);
                lhsEval += parseInt(wordValStr);
                equationPart += `${wordValStr} + `;
            });
            equationPart = equationPart.slice(0, -3);
            let rhsValStr = "";
            for (const char of puzzleInstance.rhs) rhsValStr += sol.get(char);
            equationPart += ` = ${rhsValStr}`;
            solutionsText += `${line}  (${equationPart})\n\n`;
        });
        solutionsList.textContent = solutionsText;

        // Add a final state showing the first solution found
        visualizationStates.push({
            assignments: allSolutions[0], // Show the first solution on the board
            domains: new Map(),
            explanation: `Search completed. Found ${allSolutions.length} solution(s). Displaying the first solution.`,
            highlightedVar: null,
            highlightedDigit: null,
            prunedInfo: null,
            success: true,
            failure: false
        });
    }
    
    // --- Update UI after generating all states ---
    if (visualizationStates.length > 0) {
        currentStep = 0;
        renderState(currentStep); // Start by showing the first state
        nextStepBtn.disabled = visualizationStates.length <= 1;
        lastStepBtn.disabled = visualizationStates.length <= 1;
        prevStepBtn.disabled = true;
    }
}


// --- UI Rendering Functions ---
function renderPuzzle() {
    if (!puzzleInstance) {
        puzzleDisplay.innerHTML = '';
        return;
    }
    let equationHtml = puzzleInstance.lhs.join(' + ') + ' = ' + puzzleInstance.rhs;
    puzzleDisplay.textContent = equationHtml;
}

function renderState(step) {
    if (step < 0 || step >= visualizationStates.length) return;

    const state = visualizationStates[step];

    // Render current assignments
    assignmentDisplay.innerHTML = '';
    let previousAssignments = currentStep > 0 ? visualizationStates[currentStep -1].assignments : new Map();

    for (const [char, digit] of state.assignments.entries()) {
        const item = document.createElement('div');
        item.classList.add('assignment-item');
        if (digit !== -1) {
            item.textContent = `${char}=${digit}`;
            // Highlight if this assignment just changed from the previous step
            if (previousAssignments.get(char) !== digit) {
                 item.classList.add('changed');
            }
        } else {
            item.textContent = `${char}=?`;
            item.classList.add('unassigned');
        }
        assignmentDisplay.appendChild(item);
    }
    
    // Render domains
    domainsGrid.innerHTML = '';
    for (let i = 0; i < letters.length; i++) {
        const char = letters[i];
        const domainItem = document.createElement('div');
        domainItem.classList.add('domain-item');
        if (state.highlightedVar === char) {
            domainItem.classList.add('active');
        }

        const letterSpan = document.createElement('div');
        letterSpan.classList.add('letter');
        letterSpan.textContent = char;
        domainItem.appendChild(letterSpan);

        const digitsContainer = document.createElement('div');
        digitsContainer.classList.add('digits');
        const currentDomainDigits = state.domains.get(char) || [];
        const initialFullDomain = new Array(10).fill(0).map((_,d)=>d); // digits 0-9

        for (const d of initialFullDomain) { // Always show 0-9 for each, mark removed
            const digitSpan = document.createElement('span');
            digitSpan.classList.add('digit');
            digitSpan.textContent = d;
            if (!currentDomainDigits.includes(d)) {
                digitSpan.classList.add('removed');
            }
            if (state.highlightedVar === char && state.highlightedDigit === d) {
                digitSpan.classList.add('active-val');
            }
            // Check for explicit prune info for this variable
            if (state.prunedInfo && state.prunedInfo.var === char) {
                if (Array.isArray(state.prunedInfo.digits) && state.prunedInfo.digits.includes(d) && currentDomainDigits.includes(d)) {
                     // This means a digit was explicitly pruned, but is still showing in *current* domain
                     // This indicates a visualization logic bug or the pruning was undone in previous step
                     // For AC-3, it means it's been removed in this step.
                     digitSpan.classList.add('removed-now'); // Can add a different visual for "removed in this step"
                } else if (state.prunedInfo.digit === d && !currentDomainDigits.includes(d)) {
                     digitSpan.classList.add('removed-now');
                }
            }

            digitsContainer.appendChild(digitSpan);
        }
        domainItem.appendChild(digitsContainer);
        domainsGrid.appendChild(domainItem);
    }

    stepExplanation.textContent = state.explanation;

    // Update step controls
    prevStepBtn.disabled = step === 0;
    const isLastStep = step === visualizationStates.length - 1;
    nextStepBtn.disabled = isLastStep;
    lastStepBtn.disabled = isLastStep;
    currentStep = step;
}

// --- Event Listeners ---
solveBtn.addEventListener('click', () => {
    solveBtn.disabled = true;
    resetBtn.disabled = true;
    prevStepBtn.disabled = true;
    nextStepBtn.disabled = true;
    lastStepBtn.disabled = true; 
    solutionsList.textContent = "Solving...";
    
    // Update config from UI toggles
    config.USE_AC3 = toggleAC3.checked;
    config.USE_WEIGHT_ORDER = toggleWeightOrder.checked;
    config.USE_BOUNDS_PRUNE = toggleBoundsPrune.checked;
    config.USE_CARRY_CHECK = toggleCarryCheck.checked;
    config.STOP_AFTER_FIRST = toggleStopAfterFirst.checked;

    findSolutionsWrapper();
    solveBtn.disabled = false;
    resetBtn.disabled = false;
});

resetBtn.addEventListener('click', () => {
    puzzleInput.value = "SEND + MORE = MONEY";
    visualizationStates = [];
    currentStep = -1;
    allSolutions = [];
    puzzleInstance = null;
    renderPuzzle();
    assignmentDisplay.innerHTML = '';
    domainsGrid.innerHTML = '';
    stepExplanation.textContent = "Click 'Solve' to begin the visualization.";
    solutionsList.textContent = "No solutions found yet.";
    prevStepBtn.disabled = true;
    nextStepBtn.disabled = true;
    lastStepBtn.disabled = true; 
    solveBtn.disabled = false;
});

prevStepBtn.addEventListener('click', () => {
    if (currentStep > 0) {
        renderState(currentStep - 1);
    }
});

nextStepBtn.addEventListener('click', () => {
    if (currentStep < visualizationStates.length - 1) {
        renderState(currentStep + 1);
    }
});

lastStepBtn.addEventListener('click', () => {
    if (visualizationStates.length > 0) {
        renderState(visualizationStates.length - 1);
    }
});

// Initial render
renderPuzzle();