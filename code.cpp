// ==========================================================================
// Mini-C LL(1) Predictive Parser
// ==========================================================================
// A complete, table-driven LL(1) predictive parser for a Mini-C language
// subset. Performs syntax validation and parse tree construction only.
//
// Architecture (5 sequential phases):
//   1. Grammar definition (CFG stored as data structures)
//   2. Left-recursion elimination (algorithmic)
//   3. Left-factoring (algorithmic)
//   4. FIRST / FOLLOW set computation (memoized / fixed-point)
//   5. LL(1) parse table construction -> parse token stream -> Parse Tree
// ==========================================================================
#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <set>
#include <stack>
#include <algorithm>
#include <sstream>
#include <iomanip>
using namespace std;
// --------------------------------------------------------------------------
// Type Definitions
// --------------------------------------------------------------------------
using Production = vector<string>;
using Grammar    = map<string, vector<Production>>;
// --------------------------------------------------------------------------
// Parse Tree Node
// --------------------------------------------------------------------------
struct ParseNode {
    string symbol;              // Terminal or non-terminal name
    string tokenValue;          // Actual token value (for terminals)
    vector<ParseNode*> children;
    ParseNode(const string& sym) : symbol(sym) {}
    ~ParseNode() {
        for (auto* child : children)
            delete child;
    }
};
// --------------------------------------------------------------------------
// Global Data
// --------------------------------------------------------------------------
map<string, set<string>>              firstSets;
map<string, set<string>>              followSets;
map<string, map<string, Production>>  parseTable;
set<string>                           firstComputing;   // cycle guard
const string EPSILON      = "eps";
const string END_MARKER   = "$";
const string START_SYMBOL = "Program";
// --------------------------------------------------------------------------
// Utility Functions
// --------------------------------------------------------------------------
bool isNonTerminal(const string& sym, const Grammar& g) {
    return g.count(sym) > 0;
}
bool isTerminal(const string& sym, const Grammar& g) {
    return sym != EPSILON && !isNonTerminal(sym, g);
}
string productionToString(const Production& prod) {
    string r;
    for (size_t i = 0; i < prod.size(); i++) {
        if (i) r += " ";
        r += prod[i];
    }
    return r;
}
void printGrammar(const Grammar& g, const string& title) {
    cout << "\n" << string(64, '=') << "\n"
         << title << "\n"
         << string(64, '=') << endl;
    for (const auto& [nt, prods] : g) {
        for (size_t i = 0; i < prods.size(); i++) {
            if (i == 0)
                cout << "  " << left << setw(18) << nt
                     << " -> " << productionToString(prods[i]) << "\n";
            else
                cout << "  " << string(18, ' ')
                     << "  | " << productionToString(prods[i]) << "\n";
        }
    }
    cout << flush;
}
// ==========================================================================
// Phase 1 — Grammar Definition
// ==========================================================================
Grammar defineGrammar() {
    Grammar g;
    // Program / top-level declarations
    g["Program"]       = { {"DeclList"} };
    g["DeclList"]      = { {"Decl", "DeclList"}, {EPSILON} };
    g["Decl"]          = { {"Type", "ID", "DeclTail"} };
    g["DeclTail"]      = { {"(", "ParamList", ")", "Block"},
                           {"VarTail", ";"} };
    g["VarTail"]       = { {"=", "Expr"}, {EPSILON} };
    // Types
    g["Type"]          = { {"int"}, {"float"}, {"void"} };
    // Parameters
    g["ParamList"]     = { {"ParamListTail"}, {EPSILON} };
    g["ParamListTail"] = { {"Param", "ParamRest"} };
    g["ParamRest"]     = { {",", "Param", "ParamRest"}, {EPSILON} };
    g["Param"]         = { {"Type", "ID"} };
    // Blocks & statements
    g["Block"]         = { {"{", "StmtList", "}"} };
    g["StmtList"]      = { {"Stmt", "StmtList"}, {EPSILON} };
    g["Stmt"]          = {
        {"Type", "ID", "VarTail", ";"},
        {"ID", "StmtTail"},
        {"if", "(", "Expr", ")", "Block", "ElsePart"},
        {"while", "(", "Expr", ")", "Block"},
        {"for", "(", "ForInit", ";", "ForCond", ";", "ForUpdate", ")", "Block"},
        {"return", "ReturnVal", ";"},
        {"Block"}
    };
    g["StmtTail"]      = { {"=", "Expr", ";"}, {"(", "ArgList", ")", ";"} };
    g["ElsePart"]      = { {"else", "Block"}, {EPSILON} };
    // For-loop components
    g["ForInit"]       = { {"Type", "ID", "=", "Expr"},
                           {"ID", "=", "Expr"},
                           {EPSILON} };
    g["ForCond"]       = { {"Expr"}, {EPSILON} };
    g["ForUpdate"]     = { {"ID", "=", "Expr"}, {EPSILON} };
    // Return
    g["ReturnVal"]     = { {"Expr"}, {EPSILON} };
    // Function arguments
    g["ArgList"]       = { {"ArgListTail"}, {EPSILON} };
    g["ArgListTail"]   = { {"Expr", "ArgRest"} };
    g["ArgRest"]       = { {",", "Expr", "ArgRest"}, {EPSILON} };
    // Expressions (operator-precedence, left-recursion eliminated)
    g["Expr"]          = { {"RelExpr"} };
    g["RelExpr"]       = { {"AddExpr", "RelExprTail"} };
    g["RelExprTail"]   = {
        {"==", "AddExpr", "RelExprTail"},
        {"!=", "AddExpr", "RelExprTail"},
        {"<",  "AddExpr", "RelExprTail"},
        {">",  "AddExpr", "RelExprTail"},
        {"<=", "AddExpr", "RelExprTail"},
        {">=", "AddExpr", "RelExprTail"},
        {EPSILON}
    };
    g["AddExpr"]       = { {"MulExpr", "AddExprTail"} };
    g["AddExprTail"]   = {
        {"+", "MulExpr", "AddExprTail"},
        {"-", "MulExpr", "AddExprTail"},
        {EPSILON}
    };
    g["MulExpr"]       = { {"UnaryExpr", "MulExprTail"} };
    g["MulExprTail"]   = {
        {"*", "UnaryExpr", "MulExprTail"},
        {"/", "UnaryExpr", "MulExprTail"},
        {EPSILON}
    };
    g["UnaryExpr"]     = { {"-", "UnaryExpr"}, {"Primary"} };
    g["Primary"]       = { {"NUM"},
                           {"(", "Expr", ")"},
                           {"ID", "PrimaryTail"} };
    g["PrimaryTail"]   = { {"(", "ArgList", ")"}, {EPSILON} };
    return g;
}
// ==========================================================================
// Phase 2 — Left-Recursion Elimination  (standard textbook algorithm)
// ==========================================================================
void eliminateLeftRecursion(Grammar& g) {
    cout << "\n--- Phase 2: Left-Recursion Elimination ---" << endl;
    vector<string> nts;
    for (const auto& [nt, _] : g) nts.push_back(nt);
    bool any = false;
    for (size_t i = 0; i < nts.size(); i++) {
        const string& Ai = nts[i];
        // Step 1 — substitute Aj (j < i) into Ai to surface indirect LR
        for (size_t j = 0; j < i; j++) {
            const string& Aj = nts[j];
            vector<Production> np;
            bool sub = false;
            for (const auto& prod : g[Ai]) {
                if (!prod.empty() && prod[0] == Aj) {
                    sub = true;
                    for (const auto& ajP : g[Aj]) {
                        Production p;
                        if (ajP.size() == 1 && ajP[0] == EPSILON) {
                            p.insert(p.end(), prod.begin() + 1, prod.end());
                            if (p.empty()) p.push_back(EPSILON);
                        } else {
                            p = ajP;
                            p.insert(p.end(), prod.begin() + 1, prod.end());
                        }
                        np.push_back(p);
                    }
                } else {
                    np.push_back(prod);
                }
            }
            if (sub) g[Ai] = np;
        }
        // Step 2 — remove direct left recursion  A -> A alpha | beta
        vector<Production> alphas, betas;
        for (const auto& prod : g[Ai]) {
            if (!prod.empty() && prod[0] == Ai)
                alphas.emplace_back(prod.begin() + 1, prod.end());
            else
                betas.push_back(prod);
        }
        if (!alphas.empty()) {
            any = true;
            string AiP = Ai + "'";
            while (g.count(AiP)) AiP += "'";
            cout << "  Rewrote " << Ai
                 << "  (new tail non-terminal: " << AiP << ")" << endl;
            g[Ai].clear();
            for (auto& beta : betas) {
                Production p;
                if (beta.size() == 1 && beta[0] == EPSILON)
                    p = {AiP};
                else {
                    p = beta;
                    p.push_back(AiP);
                }
                g[Ai].push_back(p);
            }
            g[AiP] = {};
            for (auto& alpha : alphas) {
                alpha.push_back(AiP);
                g[AiP].push_back(alpha);
            }
            g[AiP].push_back({EPSILON});
            nts.push_back(AiP);
        }
    }
    if (!any)
        cout << "  No left recursion detected — grammar unchanged." << endl;
}
// ==========================================================================
// Phase 3 — Left Factoring  (iterative, convergent)
// ==========================================================================
void leftFactor(Grammar& g) {
    cout << "\n--- Phase 3: Left Factoring ---" << endl;
    bool anyChange = false;
    bool changed   = true;
    while (changed) {
        changed = false;
        vector<string> nts;
        for (const auto& [nt, _] : g) nts.push_back(nt);
        for (const auto& nt : nts) {
            auto& prods = g[nt];
            if (prods.size() < 2) continue;
            // Group productions by first symbol
            map<string, vector<int>> groups;
            for (int i = 0; i < (int)prods.size(); i++)
                if (!prods[i].empty() && prods[i][0] != EPSILON)
                    groups[prods[i][0]].push_back(i);
            bool factored = false;
            for (auto& [sym, idx] : groups) {
                if ((int)idx.size() < 2) continue;
                // Longest common prefix among all productions in this group
                int pLen = 0;
                bool ext = true;
                while (ext) {
                    if ((size_t)pLen >= prods[idx[0]].size()) break;
                    const string& s = prods[idx[0]][pLen];
                    for (int k : idx)
                        if ((size_t)pLen >= prods[k].size() || prods[k][pLen] != s)
                            { ext = false; break; }
                    if (ext) pLen++;
                }
                if (pLen == 0) continue;
                // New non-terminal for the suffixes
                string newNT = nt + "'";
                { int c = 1; while (g.count(newNT)) newNT = nt + "'" + to_string(c++); }
                cout << "  Factored " << nt
                     << " (prefix len " << pLen << ") -> " << newNT << endl;
                Production prefix(prods[idx[0]].begin(),
                                  prods[idx[0]].begin() + pLen);
                vector<Production> suffixes;
                for (int k : idx) {
                    Production s(prods[k].begin() + pLen, prods[k].end());
                    if (s.empty()) s = {EPSILON};
                    suffixes.push_back(s);
                }
                g[newNT] = suffixes;
                set<int> rmSet(idx.begin(), idx.end());
                vector<Production> kept;
                for (int i = 0; i < (int)prods.size(); i++)
                    if (!rmSet.count(i)) kept.push_back(prods[i]);
                Production fp = prefix;
                fp.push_back(newNT);
                kept.push_back(fp);
                g[nt] = kept;
                factored  = true;
                anyChange = true;
                changed   = true;
                break;
            }
            if (factored) break;
        }
    }
    if (!anyChange)
        cout << "  No common prefixes detected — grammar unchanged." << endl;
}
// ==========================================================================
// Phase 4a — FIRST Set Computation  (recursive, memoized)
// ==========================================================================
set<string> computeFirst(const string& symbol, const Grammar& g) {
    if (firstSets.count(symbol))    return firstSets[symbol];
    if (firstComputing.count(symbol)) return {};          // break cycle
    firstComputing.insert(symbol);
    set<string> result;
    if (!isNonTerminal(symbol, g)) {
        result.insert(symbol);                             // terminal
    } else {
        for (const auto& prod : g.at(symbol)) {
            if (prod.size() == 1 && prod[0] == EPSILON) {
                result.insert(EPSILON);
            } else {
                bool allEps = true;
                for (const auto& s : prod) {
                    if (s == EPSILON) continue;
                    auto f = computeFirst(s, g);
                    for (const auto& x : f)
                        if (x != EPSILON) result.insert(x);
                    if (!f.count(EPSILON)) { allEps = false; break; }
                }
                if (allEps) result.insert(EPSILON);
            }
        }
    }
    firstComputing.erase(symbol);
    firstSets[symbol] = result;
    return result;
}
// FIRST of a suffix  seq[start .. end)
set<string> computeFirstOfSequence(const Production& seq, int start,
                                   const Grammar& g) {
    set<string> result;
    if (start >= (int)seq.size()) { result.insert(EPSILON); return result; }
    bool allEps = true;
    for (int i = start; i < (int)seq.size(); i++) {
        if (seq[i] == EPSILON) continue;
        auto f = computeFirst(seq[i], g);
        for (const auto& x : f)
            if (x != EPSILON) result.insert(x);
        if (!f.count(EPSILON)) { allEps = false; break; }
    }
    if (allEps) result.insert(EPSILON);
    return result;
}
void computeAllFirstSets(const Grammar& g) {
    cout << "\n--- Phase 4a: Computing FIRST Sets ---" << endl;
    firstSets.clear();
    firstComputing.clear();
    for (const auto& [nt, _] : g) computeFirst(nt, g);
    cout << "  Done (" << g.size() << " non-terminals)." << endl;
}
// ==========================================================================
// Phase 4b — FOLLOW Set Computation  (fixed-point iteration)
// ==========================================================================
void computeFollow(const Grammar& g, const string& startSym) {
    cout << "\n--- Phase 4b: Computing FOLLOW Sets ---" << endl;
    followSets.clear();
    for (const auto& [nt, _] : g) followSets[nt] = {};
    followSets[startSym].insert(END_MARKER);
    bool changed = true;
    int iter = 0;
    while (changed) {
        changed = false;
        iter++;
        for (const auto& [A, prods] : g) {
            for (const auto& prod : prods) {
                for (int i = 0; i < (int)prod.size(); i++) {
                    const string& B = prod[i];
                    if (!isNonTerminal(B, g)) continue;
                    auto fb = computeFirstOfSequence(prod, i + 1, g);
                    for (const auto& t : fb)
                        if (t != EPSILON && !followSets[B].count(t))
                            { followSets[B].insert(t); changed = true; }
                    if (fb.count(EPSILON))
                        for (const auto& t : followSets[A])
                            if (!followSets[B].count(t))
                                { followSets[B].insert(t); changed = true; }
                }
            }
        }
    }
    cout << "  Converged after " << iter << " iteration(s)." << endl;
}
// ==========================================================================
// Phase 5 — LL(1) Parse Table Construction
// ==========================================================================
void buildParseTable(const Grammar& g) {
    cout << "\n--- Phase 5: Building LL(1) Parse Table ---" << endl;
    parseTable.clear();
    bool conflict = false;
    for (const auto& [A, prods] : g) {
        for (const auto& prod : prods) {
            set<string> fa;
            if (prod.size() == 1 && prod[0] == EPSILON)
                fa.insert(EPSILON);
            else
                fa = computeFirstOfSequence(prod, 0, g);
            // Rule 1: for each t in FIRST(alpha)\{eps}
            for (const auto& t : fa) {
                if (t == EPSILON) continue;
                if (parseTable[A].count(t) && parseTable[A][t] != prod) {
                    conflict = true;
                    cout << "  WARNING — LL(1) conflict at M[" << A
                         << ", " << t << "]:\n"
                         << "    Existing   : " << A << " -> "
                         << productionToString(parseTable[A][t]) << "\n"
                         << "    Conflicting: " << A << " -> "
                         << productionToString(prod) << endl;
                }
                parseTable[A][t] = prod;
            }
            // Rule 2: if eps in FIRST(alpha), for each t in FOLLOW(A)
            if (fa.count(EPSILON)) {
                for (const auto& t : followSets[A]) {
                    if (parseTable[A].count(t) && parseTable[A][t] != prod) {
                        conflict = true;
                        cout << "  WARNING — LL(1) conflict at M[" << A
                             << ", " << t << "]:\n"
                             << "    Existing   : " << A << " -> "
                             << productionToString(parseTable[A][t]) << "\n"
                             << "    Conflicting: " << A << " -> "
                             << productionToString(prod) << endl;
                    }
                    parseTable[A][t] = prod;
                }
            }
        }
    }
    if (!conflict)
        cout << "  No conflicts — grammar is LL(1)!" << endl;
}
// ==========================================================================
// Phase 6 — LL(1) Stack-Based Parsing with Parse-Tree Construction
//           + panic-mode error recovery (sync on  ;  }  $ )
// ==========================================================================
ParseNode* parse(const Grammar& g, const vector<string>& tokens) {
    ParseNode* root = new ParseNode(START_SYMBOL);
    stack<pair<string, ParseNode*>> stk;
    stk.push({END_MARKER, nullptr});
    stk.push({START_SYMBOL, root});
    int  idx      = 0;
    bool hasError = false;
    while (!stk.empty()) {
        auto [top, node] = stk.top();
        // --- end-marker handling ---
        if (top == END_MARKER) {
            stk.pop();
            string cur = (idx < (int)tokens.size()) ? tokens[idx] : END_MARKER;
            if (cur != END_MARKER) {
                cout << "  ERROR: expected end-of-input at index " << idx
                     << ", got '" << cur << "'" << endl;
                hasError = true;
            }
            break;
        }
        string curTok = (idx < (int)tokens.size()) ? tokens[idx] : END_MARKER;
        // --- terminal on top ---
        if (isTerminal(top, g) || top == END_MARKER) {
            stk.pop();
            if (top == curTok) {
                if (node) node->tokenValue = curTok;
                idx++;
            } else {
                // Error recovery by insertion: pop expected, don't advance
                cout << "  ERROR at index " << idx
                     << ": expected '" << top << "', got '" << curTok << "'"
                     << endl;
                hasError = true;
            }
            continue;
        }
        // --- non-terminal on top ---
        if (parseTable.count(top) && parseTable[top].count(curTok)) {
            stk.pop();
            const Production& prod = parseTable[top][curTok];
            if (prod.size() == 1 && prod[0] == EPSILON) {
                // epsilon production
                auto* ep = new ParseNode(EPSILON);
                if (node) node->children.push_back(ep);
            } else {
                vector<ParseNode*> kids;
                for (const auto& sym : prod) {
                    auto* ch = new ParseNode(sym);
                    kids.push_back(ch);
                    if (node) node->children.push_back(ch);
                }
                // push in reverse so leftmost symbol is on top
                for (int i = (int)kids.size() - 1; i >= 0; i--)
                    stk.push({prod[i], kids[i]});
            }
        } else {
            // --- parse error: no table entry ---
            cout << "  ERROR at index " << idx
                 << ": unexpected '" << curTok
                 << "' for non-terminal '" << top << "'" << endl;
            cout << "    Expected one of: ";
            if (parseTable.count(top))
                for (const auto& [t, _] : parseTable[top]) cout << "'" << t << "' ";
            else
                cout << "(no entries)";
            cout << endl;
            hasError = true;
            // Panic-mode recovery: skip input to synchronisation token
            const set<string> sync = {";", "}", END_MARKER};
            while (idx < (int)tokens.size() && !sync.count(tokens[idx]))
                idx++;
            if (idx < (int)tokens.size() && tokens[idx] != END_MARKER)
                idx++;                               // consume the sync token
            // Pop stack until a useful entry is found
            stk.pop();                               // pop the failed NT
            while (!stk.empty()) {
                auto& e = stk.top();
                if (e.first == END_MARKER) break;
                string c = (idx < (int)tokens.size()) ? tokens[idx] : END_MARKER;
                if (isTerminal(e.first, g) && e.first == c)               break;
                if (isNonTerminal(e.first, g)
                    && parseTable.count(e.first)
                    && parseTable[e.first].count(c))                       break;
                stk.pop();
            }
        }
    }
    cout << (hasError ? "  Parse completed with errors."
                      : "  Parse successful!") << endl;
    return root;
}
// ==========================================================================
// Phase 7 — Parse Tree Pretty-Printing
// ==========================================================================
void printParseTree(ParseNode* root, int depth) {
    if (!root) return;
    string indent(depth * 2, ' ');
    if (root->symbol == EPSILON) {
        cout << indent << "epsilon" << endl;
    } else if (root->children.empty()) {
        // Terminal leaf node (or unexpanded node from error recovery)
        cout << indent << "[" << root->symbol << "]" << endl;
    } else {
        // Non-terminal internal node
        cout << indent << root->symbol << endl;
        for (auto* child : root->children)
            printParseTree(child, depth + 1);
    }
}
// ==========================================================================
// Display Helpers
// ==========================================================================
void printFirstSets(const Grammar& g) {
    cout << "\n" << string(64, '=') << "\n"
         << "FIRST Sets\n"
         << string(64, '=') << endl;
    for (const auto& [nt, _] : g) {
        cout << "  FIRST(" << left << setw(17) << nt << ") = { ";
        bool f = true;
        for (const auto& s : firstSets[nt]) {
            if (!f) cout << ", ";
            cout << s;
            f = false;
        }
        cout << " }" << endl;
    }
}
void printFollowSets(const Grammar& g) {
    cout << "\n" << string(64, '=') << "\n"
         << "FOLLOW Sets\n"
         << string(64, '=') << endl;
    for (const auto& [nt, _] : g) {
        cout << "  FOLLOW(" << left << setw(16) << nt << ") = { ";
        bool f = true;
        for (const auto& s : followSets[nt]) {
            if (!f) cout << ", ";
            cout << s;
            f = false;
        }
        cout << " }" << endl;
    }
}
void printParseTableFormatted() {
    cout << "\n" << string(64, '=') << "\n"
         << "LL(1) Parse Table\n"
         << string(64, '=') << endl;
    int count = 0;
    for (const auto& [nt, entries] : parseTable) {
        for (const auto& [t, prod] : entries) {
            cout << "  M[" << left << setw(16) << nt
                 << ", " << setw(7) << t << "] = "
                 << nt << " -> " << productionToString(prod) << endl;
            count++;
        }
    }
    cout << "  (" << count << " total entries)" << endl;
}
// ==========================================================================
// Main — exercise all phases and run 3 test cases
// ==========================================================================
int main() {
    cout << string(64, '*') << "\n"
         << "*   Mini-C LL(1) Predictive Parser                             *\n"
         << "*   Grammar-Driven Syntax Validator + Parse Tree Builder       *\n"
         << string(64, '*') << endl;
    // ---- Phase 1 ----
    Grammar g = defineGrammar();
    printGrammar(g, "Phase 1: Original Mini-C Grammar");
    // ---- Phase 2 ----
    eliminateLeftRecursion(g);
    // ---- Phase 3 ----
    leftFactor(g);
    // ---- Phase 4 ----
    computeAllFirstSets(g);
    computeFollow(g, START_SYMBOL);
    printFirstSets(g);
    printFollowSets(g);
    // ---- Phase 5 ----
    buildParseTable(g);
    printParseTableFormatted();
    // ==================================================================
    //  Test Cases
    // ==================================================================
    cout << "\n" << string(64, '=') << "\n"
         << "PARSING TEST CASES\n"
         << string(64, '=') << endl;
    // ------------------------------------------------------------------
    // Case 1: valid function with nested if and while
    // ------------------------------------------------------------------
    {
        cout << "\n------ Test Case 1: function with nested if/while ------\n";
        vector<string> tokens = {
            "int", "ID", "(", "int", "ID", ")", "{",
            "int", "ID", "=", "NUM", ";",
            "if", "(", "ID", "<", "NUM", ")", "{",
            "while", "(", "ID", ">", "NUM", ")", "{",
            "ID", "=", "ID", "+", "NUM", ";",
            "}", "}", "return", "ID", ";", "}", "$"
        };
        cout << "Tokens: ";
        for (const auto& t : tokens) cout << t << " ";
        cout << "\n\n";
        ParseNode* tree = parse(g, tokens);
        cout << "\nParse Tree:\n";
        printParseTree(tree, 0);
        delete tree;
    }
    // ------------------------------------------------------------------
    // Case 2: function call inside expression
    // ------------------------------------------------------------------
    {
        cout << "\n------ Test Case 2: function call inside expression ------\n";
        vector<string> tokens = {
            "int", "ID", "(", ")", "{",
            "ID", "=", "ID", "(", "NUM", ",", "ID", ")", ";",
            "return", "NUM", ";", "}", "$"
        };
        cout << "Tokens: ";
        for (const auto& t : tokens) cout << t << " ";
        cout << "\n\n";
        ParseNode* tree = parse(g, tokens);
        cout << "\nParse Tree:\n";
        printParseTree(tree, 0);
        delete tree;
    }
    // ------------------------------------------------------------------
    // Case 3: syntax error — missing semicolon
    // ------------------------------------------------------------------
    {
        cout << "\n------ Test Case 3: syntax error (missing semicolon) ------\n";
        vector<string> tokens = {"int", "ID", "=", "NUM", "$"};
        cout << "Tokens: ";
        for (const auto& t : tokens) cout << t << " ";
        cout << "\n\n";
        ParseNode* tree = parse(g, tokens);
        cout << "\nParse Tree:\n";
        printParseTree(tree, 0);
        delete tree;
    }
    return 0;
}
