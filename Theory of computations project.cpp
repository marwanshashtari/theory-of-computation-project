// ============================================================================
// Simple Mini-C LL(1) Parser
// ============================================================================
// This project is a simplified character-based syntax parser for a small
// Mini-C-like language. It does NOT use tokenizing / lexical analysis.
//
// Instead of writing real C keywords, the user writes one-character symbols:
//
//   t = int/type declaration
//   i = identifier / variable name
//   n = number
//   f = for
//   c = if
//   e = else
//   b = break
//   r = return
//   ~ = equality comparison ==
//   ! = not-equal comparison !=
//
// Example real C-style code:
//   for (int x = 0; x < 5; x = x + 1) { if (x != 5) { break; } }
//
// Simplified input accepted by this parser:
//   f(ti=n;i<n;i=i+n){c(i!n){b;}}
//
// Compiler-design aspects included:
//   1. Grammar stored as production rules
//   2. Automatic direct/indirect left-recursion elimination
//   3. FIRST set computation
//   4. FOLLOW set computation
//   5. LL(1) parse-table construction
//   6. Stack-based predictive parsing
//
// This parser checks syntax only. It does not check semantic errors such as
// using undeclared variables, declaring the same variable twice, or using break
// outside a loop.
// ============================================================================

#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <set>
#include <stack>
#include <iomanip>
#include <algorithm>
#include <cctype>

using namespace std;

using Production = vector<string>;
using Grammar = map<string, vector<Production>>;

const string EPSILON = "eps";
const string END_MARKER = "$";
const string START_SYMBOL = "Program";

map<string, set<string>> firstSets;
map<string, set<string>> followSets;
map<string, map<string, Production>> parseTable;
set<string> firstComputing;

// ----------------------------------------------------------------------------
// Basic helper functions
// ----------------------------------------------------------------------------

bool isNonTerminal(const string& symbol, const Grammar& grammar) {
    return grammar.count(symbol) > 0;
}

bool isTerminal(const string& symbol, const Grammar& grammar) {
    return symbol != EPSILON && !isNonTerminal(symbol, grammar);
}

string productionToString(const Production& production) {
    string result;
    for (size_t i = 0; i < production.size(); i++) {
        if (i > 0) result += " ";
        result += production[i];
    }
    return result;
}

void printGrammar(const Grammar& grammar, const string& title) {
    cout << "\n" << title << "\n";
    cout << string(60, '=') << "\n";

    for (const auto& rule : grammar) {
        const string& leftSide = rule.first;
        const vector<Production>& productions = rule.second;

        for (size_t i = 0; i < productions.size(); i++) {
            if (i == 0) {
                cout << left << setw(24) << leftSide << " -> "
                     << productionToString(productions[i]) << "\n";
            } else {
                cout << left << setw(24) << " " << " |  "
                     << productionToString(productions[i]) << "\n";
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Grammar definition
// ----------------------------------------------------------------------------
//
// User symbols:
//   t = int declaration
//   i = identifier
//   n = number
//   f = for
//   c = if
//   e = else
//   b = break
//   r = return
//   ~ = ==
//   ! = !=
//
// Main language examples:
//   t i;                         int x;
//   t i=n;                       int x = 5;
//   i=n;                         x = 5;
//   i=i+n;                       x = x + 5;
//   b;                           break;
//   r;                           return;
//   r n;                         return 5;
//   c(i<n){b;}                   if (x < 5) { break; }
//   c(i!n){b;}e{r;}              if (x != 5) { break; } else { return; }
//   f(ti=n;i<n;i=i+n){b;}        for (int x = 5; x < 5; x = x + 5) { break; }
//
// Expression and Term are intentionally written with left recursion:
//   Expression -> Expression + Term | Expression - Term | ... | Term
//   Term       -> Term * Factor | Term / Factor | Factor
//
// The program eliminates this left recursion before building the parse table.
// ----------------------------------------------------------------------------

Grammar defineGrammar() {
    Grammar grammar;

    grammar["Program"] = {
        {"StatementList"}
    };

    grammar["StatementList"] = {
        {"Statement", "StatementList"},
        {EPSILON}
    };

    grammar["Statement"] = {
        {"Declaration"},
        {"Assignment"},
        {"BreakStatement"},
        {"ReturnStatement"},
        {"ForStatement"},
        {"IfStatement"},
        {"Block"}
    };

    // t i; or t i=n;
    grammar["Declaration"] = {
        {"t", "i", "DeclarationTail"}
    };

    grammar["DeclarationTail"] = {
        {";"},
        {"=", "Expression", ";"}
    };

    // i=n;
    grammar["Assignment"] = {
        {"i", "=", "Expression", ";"}
    };

    // i=n       used inside for-loop header without semicolon
    // t i=n     used inside for-loop header as integer declaration
    grammar["ForInit"] = {
        {"AssignmentNoSemicolon"},
        {"DeclarationNoSemicolon"},
        {EPSILON}
    };

    grammar["AssignmentNoSemicolon"] = {
        {"i", "=", "Expression"}
    };

    grammar["DeclarationNoSemicolon"] = {
        {"t", "i", "=", "Expression"}
    };

    grammar["ForCondition"] = {
        {"Expression"},
        {EPSILON}
    };

    grammar["ForUpdate"] = {
        {"AssignmentNoSemicolon"},
        {EPSILON}
    };

    grammar["BreakStatement"] = {
        {"b", ";"}
    };

    grammar["ReturnStatement"] = {
        {"r", "ReturnValue", ";"}
    };

    grammar["ReturnValue"] = {
        {"Expression"},
        {EPSILON}
    };

    grammar["ForStatement"] = {
        {"f", "(", "ForInit", ";", "ForCondition", ";", "ForUpdate", ")", "Block"}
    };

    grammar["IfStatement"] = {
        {"c", "(", "Expression", ")", "Block", "ElsePart"}
    };

    grammar["ElsePart"] = {
        {"e", "Block"},
        {EPSILON}
    };

    grammar["Block"] = {
        {"{", "StatementList", "}"}
    };

    // Left-recursive expression grammar.
    grammar["Expression"] = {
        {"Expression", "+", "Term"},
        {"Expression", "-", "Term"},
        {"Expression", "<", "Term"},
        {"Expression", ">", "Term"},
        {"Expression", "~", "Term"},
        {"Expression", "!", "Term"},
        {"Term"}
    };

    grammar["Term"] = {
        {"Term", "*", "Factor"},
        {"Term", "/", "Factor"},
        {"Factor"}
    };

    grammar["Factor"] = {
        {"i"},
        {"n"},
        {"(", "Expression", ")"}
    };

    return grammar;
}

// ----------------------------------------------------------------------------
// Left-recursion elimination
// ----------------------------------------------------------------------------

void eliminateLeftRecursion(Grammar& grammar) {
    vector<string> nonTerminals;

    for (const auto& rule : grammar) {
        nonTerminals.push_back(rule.first);
    }

    for (size_t i = 0; i < nonTerminals.size(); i++) {
        string Ai = nonTerminals[i];

        // Replace Ai -> Aj gamma using productions of Aj, for j < i.
        for (size_t j = 0; j < i; j++) {
            string Aj = nonTerminals[j];
            vector<Production> newProductions;

            for (const Production& production : grammar[Ai]) {
                if (!production.empty() && production[0] == Aj) {
                    for (const Production& AjProduction : grammar[Aj]) {
                        Production combined;

                        if (!(AjProduction.size() == 1 && AjProduction[0] == EPSILON)) {
                            combined.insert(combined.end(), AjProduction.begin(), AjProduction.end());
                        }

                        combined.insert(combined.end(), production.begin() + 1, production.end());

                        if (combined.empty()) {
                            combined.push_back(EPSILON);
                        }

                        newProductions.push_back(combined);
                    }
                } else {
                    newProductions.push_back(production);
                }
            }

            grammar[Ai] = newProductions;
        }

        // Remove direct left recursion Ai -> Ai alpha | beta.
        vector<Production> alphaRules;
        vector<Production> betaRules;

        for (const Production& production : grammar[Ai]) {
            if (!production.empty() && production[0] == Ai) {
                Production alpha(production.begin() + 1, production.end());
                alphaRules.push_back(alpha);
            } else {
                betaRules.push_back(production);
            }
        }

        if (!alphaRules.empty()) {
            string newNonTerminal = Ai + "Tail";
            while (grammar.count(newNonTerminal)) {
                newNonTerminal += "Tail";
            }

            grammar[Ai].clear();

            for (Production beta : betaRules) {
                if (beta.size() == 1 && beta[0] == EPSILON) {
                    grammar[Ai].push_back({newNonTerminal});
                } else {
                    beta.push_back(newNonTerminal);
                    grammar[Ai].push_back(beta);
                }
            }

            grammar[newNonTerminal] = {};

            for (Production alpha : alphaRules) {
                alpha.push_back(newNonTerminal);
                grammar[newNonTerminal].push_back(alpha);
            }

            grammar[newNonTerminal].push_back({EPSILON});
            nonTerminals.push_back(newNonTerminal);
        }
    }
}

// ----------------------------------------------------------------------------
// FIRST set computation
// ----------------------------------------------------------------------------

set<string> computeFirst(const string& symbol, const Grammar& grammar) {
    if (firstSets.count(symbol)) {
        return firstSets[symbol];
    }

    if (firstComputing.count(symbol)) {
        return {};
    }

    firstComputing.insert(symbol);
    set<string> result;

    if (!isNonTerminal(symbol, grammar)) {
        result.insert(symbol);
    } else {
        for (const Production& production : grammar.at(symbol)) {
            if (production.size() == 1 && production[0] == EPSILON) {
                result.insert(EPSILON);
            } else {
                bool allCanBeEpsilon = true;

                for (const string& currentSymbol : production) {
                    if (currentSymbol == EPSILON) {
                        continue;
                    }

                    set<string> currentFirst = computeFirst(currentSymbol, grammar);

                    for (const string& item : currentFirst) {
                        if (item != EPSILON) {
                            result.insert(item);
                        }
                    }

                    if (!currentFirst.count(EPSILON)) {
                        allCanBeEpsilon = false;
                        break;
                    }
                }

                if (allCanBeEpsilon) {
                    result.insert(EPSILON);
                }
            }
        }
    }

    firstComputing.erase(symbol);
    firstSets[symbol] = result;
    return result;
}

set<string> computeFirstOfSequence(const Production& sequence, int startIndex, const Grammar& grammar) {
    set<string> result;

    if (startIndex >= (int)sequence.size()) {
        result.insert(EPSILON);
        return result;
    }

    bool allCanBeEpsilon = true;

    for (int i = startIndex; i < (int)sequence.size(); i++) {
        string symbol = sequence[i];

        if (symbol == EPSILON) {
            continue;
        }

        set<string> symbolFirst = computeFirst(symbol, grammar);

        for (const string& item : symbolFirst) {
            if (item != EPSILON) {
                result.insert(item);
            }
        }

        if (!symbolFirst.count(EPSILON)) {
            allCanBeEpsilon = false;
            break;
        }
    }

    if (allCanBeEpsilon) {
        result.insert(EPSILON);
    }

    return result;
}

void computeAllFirstSets(const Grammar& grammar) {
    firstSets.clear();
    firstComputing.clear();

    for (const auto& rule : grammar) {
        computeFirst(rule.first, grammar);
    }
}

// ----------------------------------------------------------------------------
// FOLLOW set computation
// ----------------------------------------------------------------------------

void computeFollowSets(const Grammar& grammar) {
    followSets.clear();

    for (const auto& rule : grammar) {
        followSets[rule.first] = {};
    }

    followSets[START_SYMBOL].insert(END_MARKER);

    bool changed = true;

    while (changed) {
        changed = false;

        for (const auto& rule : grammar) {
            const string& leftSide = rule.first;
            const vector<Production>& productions = rule.second;

            for (const Production& production : productions) {
                for (int i = 0; i < (int)production.size(); i++) {
                    string currentSymbol = production[i];

                    if (!isNonTerminal(currentSymbol, grammar)) {
                        continue;
                    }

                    set<string> firstOfRest = computeFirstOfSequence(production, i + 1, grammar);

                    for (const string& item : firstOfRest) {
                        if (item != EPSILON && !followSets[currentSymbol].count(item)) {
                            followSets[currentSymbol].insert(item);
                            changed = true;
                        }
                    }

                    if (firstOfRest.count(EPSILON)) {
                        for (const string& item : followSets[leftSide]) {
                            if (!followSets[currentSymbol].count(item)) {
                                followSets[currentSymbol].insert(item);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Parse table construction
// ----------------------------------------------------------------------------

bool buildParseTable(const Grammar& grammar) {
    parseTable.clear();
    bool hasConflict = false;

    for (const auto& rule : grammar) {
        const string& leftSide = rule.first;
        const vector<Production>& productions = rule.second;

        for (const Production& production : productions) {
            set<string> firstOfProduction = computeFirstOfSequence(production, 0, grammar);

            for (const string& terminal : firstOfProduction) {
                if (terminal == EPSILON) {
                    continue;
                }

                if (parseTable[leftSide].count(terminal) && parseTable[leftSide][terminal] != production) {
                    cout << "Conflict at M[" << leftSide << ", " << terminal << "]\n";
                    hasConflict = true;
                }

                parseTable[leftSide][terminal] = production;
            }

            if (firstOfProduction.count(EPSILON)) {
                for (const string& terminal : followSets[leftSide]) {
                    if (parseTable[leftSide].count(terminal) && parseTable[leftSide][terminal] != production) {
                        cout << "Conflict at M[" << leftSide << ", " << terminal << "]\n";
                        hasConflict = true;
                    }

                    parseTable[leftSide][terminal] = production;
                }
            }
        }
    }

    return !hasConflict;
}

// ----------------------------------------------------------------------------
// Predictive parsing
// ----------------------------------------------------------------------------

vector<string> inputToSymbols(const string& input) {
    vector<string> symbols;

    for (char ch : input) {
        if (isspace((unsigned char)ch)) {
            continue;
        }

        symbols.push_back(string(1, ch));
    }

    symbols.push_back(END_MARKER);
    return symbols;
}

bool parseInput(const Grammar& grammar, const vector<string>& inputSymbols) {
    stack<string> parserStack;

    parserStack.push(END_MARKER);
    parserStack.push(START_SYMBOL);

    int index = 0;

    while (!parserStack.empty()) {
        string top = parserStack.top();
        string currentInput = inputSymbols[index];

        if (top == END_MARKER && currentInput == END_MARKER) {
            return true;
        }

        if (isTerminal(top, grammar) || top == END_MARKER) {
            if (top == currentInput) {
                parserStack.pop();
                index++;
            } else {
                cout << "Syntax Error: expected '" << top
                     << "' but found '" << currentInput << "'.\n";
                return false;
            }
        } else {
            if (parseTable.count(top) && parseTable[top].count(currentInput)) {
                Production production = parseTable[top][currentInput];
                parserStack.pop();

                if (!(production.size() == 1 && production[0] == EPSILON)) {
                    for (int i = (int)production.size() - 1; i >= 0; i--) {
                        parserStack.push(production[i]);
                    }
                }
            } else {
                cout << "Syntax Error near '" << currentInput
                     << "'. No rule for non-terminal '" << top << "'.\n";

                if (parseTable.count(top)) {
                    cout << "Expected one of: ";
                    for (const auto& entry : parseTable[top]) {
                        cout << "'" << entry.first << "' ";
                    }
                    cout << "\n";
                }

                return false;
            }
        }
    }

    return false;
}

// ----------------------------------------------------------------------------
// Printing FIRST and FOLLOW sets
// ----------------------------------------------------------------------------

void printFirstSets() {
    cout << "\nFIRST Sets\n";
    cout << string(60, '=') << "\n";

    for (const auto& entry : firstSets) {
        cout << left << setw(24) << entry.first << " = { ";

        bool firstItem = true;
        for (const string& item : entry.second) {
            if (!firstItem) cout << ", ";
            cout << item;
            firstItem = false;
        }

        cout << " }\n";
    }
}

void printFollowSets() {
    cout << "\nFOLLOW Sets\n";
    cout << string(60, '=') << "\n";

    for (const auto& entry : followSets) {
        cout << left << setw(24) << entry.first << " = { ";

        bool firstItem = true;
        for (const string& item : entry.second) {
            if (!firstItem) cout << ", ";
            cout << item;
            firstItem = false;
        }

        cout << " }\n";
    }
}

void printSymbolGuide() {
    cout << "\nSimplified Mini-C Symbol Guide\n";
    cout << string(60, '=') << "\n";

    cout << "t  = int/type declaration\n";
    cout << "i  = identifier / variable name\n";
    cout << "n  = number\n";
    cout << "f  = for\n";
    cout << "c  = if\n";
    cout << "e  = else\n";
    cout << "b  = break\n";
    cout << "r  = return\n";
    cout << "+  = addition\n";
    cout << "-  = subtraction\n";
    cout << "*  = multiplication\n";
    cout << "/  = division\n";
    cout << "<  = less than\n";
    cout << ">  = greater than\n";
    cout << "~  = equality comparison ==\n";
    cout << "!  = not-equal comparison !=\n";
    cout << "=  = assignment\n";
    cout << ";  = statement separator / semicolon\n";
    cout << "( ) = parentheses\n";
    cout << "{ } = block braces\n";

    cout << "\nAllowed input symbols:\n";
    cout << "  t i n f c e b r = + - * / < > ~ ! ; ( ) { }\n";

    cout << "\nAccepted examples:\n";
    cout << "  t i;\n";
    cout << "  t i=n;\n";
    cout << "  i=n;\n";
    cout << "  i=i+n;\n";
    cout << "  i=(i+n)*n;\n";
    cout << "  b;\n";
    cout << "  r;\n";
    cout << "  r n;\n";
    cout << "  {t i=n;i=i+n;b;}\n";
    cout << "  c(i<n){b;}\n";
    cout << "  c(i~n){b;}\n";
    cout << "  c(i!n){b;}e{r;}\n";
    cout << "  f(i=n;i<n;i=i+n){b;}\n";
    cout << "  f(ti=n;i!n;i=i+n){c(i~n){b;}e{r;}}\n";

    cout << "\nUnsupported examples:\n";
    cout << "  for(int i=0;i<5;i=i+1){break;}   // real words are not used\n";
    cout << "  int x;                            // use t i; instead\n";
    cout << "  i++;                              // ++ is not in the grammar\n";
    cout << "  c(i<=n){b;}                       // <= is not in the grammar\n";
    cout << "  char x;                           // only integer declaration t is supported\n";
}

// ----------------------------------------------------------------------------
// Main program
// ----------------------------------------------------------------------------

int main() {
    cout << "Simple Mini-C LL(1) Parser\n";
    cout << string(60, '=') << "\n";

    Grammar grammar = defineGrammar();

    printGrammar(grammar, "Original Grammar Before Left Recursion Elimination");

    eliminateLeftRecursion(grammar);

    printGrammar(grammar, "Grammar After Left Recursion Elimination");

    computeAllFirstSets(grammar);
    computeFollowSets(grammar);

    printFirstSets();
    printFollowSets();

    bool isLL1 = buildParseTable(grammar);

    if (isLL1) {
        cout << "\nParse table built successfully. Grammar is LL(1).\n";
    } else {
        cout << "\nParse table has conflicts. Grammar is not LL(1).\n";
    }

    printSymbolGuide();

    cout << "\nEnter simplified Mini-C code. Type exit to stop.\n";

    string input;

    while (true) {
        cout << "\nInput: ";
        getline(cin, input);

        if (input == "exit") {
            break;
        }

        vector<string> inputSymbols = inputToSymbols(input);
        bool accepted = parseInput(grammar, inputSymbols);

        if (accepted) {
            cout << "Result: Syntax Accepted.\n";
        } else {
            cout << "Result: Syntax Error.\n";
        }
    }

    return 0;
}
