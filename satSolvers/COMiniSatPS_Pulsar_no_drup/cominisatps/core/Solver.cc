/***************************************************************************************[Solver.cc]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>

#include "mtl/Sort.h"
#include "core/Solver.h"

using namespace Minisat;

#ifdef BIN_DRUP
int Solver::buf_len = 0;
unsigned char Solver::drup_buf[2 * 1024 * 1024];
unsigned char* Solver::buf_ptr = drup_buf;
#endif

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay_no_r    (_cat, "var-decay-no-res",   "The variable activity decay factor",            0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_var_decay_glue_r  (_cat, "var-decay-glue-res", "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    drup_file        (NULL)
  , verbosity        (0)
  , var_decay_no_r   (opt_var_decay_no_r)
  , var_decay_glue_r (opt_var_decay_glue_r)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , glucose_restart  (false)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), conflicts_glue(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , one_sided_lits(0), failed_lits(0), lit_elim(0), lit_elim2(0), lit_elim3(0), facts_enqueued(0), probed_vars(0)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc_no_r       (1)
  , var_inc_glue_r     (1)
  , watches_bin        (WatcherDeleted(ca))
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap_no_r    (VarOrderLt(activity_no_r))
  , order_heap_glue_r  (VarOrderLt(activity_glue_r))
  , progress_estimate  (0)
  , remove_satisfied   (true)

  , core_lbd_cut       (3)
  , global_lbd_sum     (0)
  , lbd_queue          (50)
  , next_T2_reduce     (10000)
  , next_L_reduce      (15000)
  
  , counter            (0)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches_bin.init(mkLit(v, false));
    watches_bin.init(mkLit(v, true ));
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    activity_no_r  .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    activity_glue_r.push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    seen2    .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);

    premise  .push(mkLit(v, false));
    premise  .push(mkLit(v, true ));
    premise_bin.push(mkLit(v, false));
    premise_bin.push(mkLit(v, true ));
    dominator.push(lit_Undef);
#if 0 && EXPERIMENTAL
    facts_tmp.push(0);
    facts_tmp_pol.push();
#endif

    // Additional space needed for stamping.
    // TODO: allocate exact memory.
    seen      .push(0);
    discovered.push(0);         discovered.push(0);
    finished  .push(0);         finished  .push(0);
    observed  .push(0);         observed  .push(0);
    flag      .push(0);         flag      .push(0);
    root      .push(lit_Undef); root      .push(lit_Undef);
    parent    .push(lit_Undef); parent    .push(lit_Undef);
    return v;
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;

    if (drup_file){
        add_oc.clear();
        for (int i = 0; i < ps.size(); i++) add_oc.push(ps[i]); }

    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (drup_file && i != j){
#ifdef BIN_DRUP
        binDRUP('a', ps, drup_file);
        binDRUP('d', add_oc, drup_file);
#else
        for (int i = 0; i < ps.size(); i++)
            fprintf(drup_file, "%i ", (var(ps[i]) + 1) * (-2 * sign(ps[i]) + 1));
        fprintf(drup_file, "0\n");

        fprintf(drup_file, "d ");
        for (int i = 0; i < add_oc.size(); i++)
            fprintf(drup_file, "%i ", (var(add_oc[i]) + 1) * (-2 * sign(add_oc[i]) + 1));
        fprintf(drup_file, "0\n");
#endif
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = c.size() == 2 ? watches_bin : watches;
    ws[~c[0]].push(Watcher(cr, c[1]));
    ws[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = c.size() == 2 ? watches_bin : watches;
    
    if (strict){
        remove(ws[~c[0]], Watcher(cr, c[1]));
        remove(ws[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        ws.smudge(~c[0]);
        ws.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr, bool skip_drup) {
    Clause& c = ca[cr];

    if (drup_file && !skip_drup){
        if (c.mark() != 1){
#ifdef BIN_DRUP
            binDRUP('d', c, drup_file);
#else
            fprintf(drup_file, "d ");
            for (int i = 0; i < c.size(); i++)
                fprintf(drup_file, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
            fprintf(drup_file, "0\n");
#endif
        }else
            printf("c Bug: removeClause(). I don't expect this to happen.\n");
    }

    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)){
        Lit implied = c.size() != 2 ? c[0] : (value(c[0]) == l_True ? c[0] : c[1]);
        vardata[var(implied)].reason = CRef_Undef; }
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
#if 0 && EXPERIMENTAL
            if (facts_tmp[x]){
                facts_tmp[x] = 0;
                facts.push(mkLit(x, facts_tmp_pol[x])); }
#endif
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
#if 0 && EXPERIMENTAL
    assert(facts.size() == 0 || !drup_file);
    while (facts.size() != 0){
        Lit p = facts.last();
        facts.pop();
        facts_tmp    [var(p)] = 1;
        facts_tmp_pol[var(p)] = sign(p);

        if (value(var(p)) == l_Undef)
            return p;
    }
#endif

    Var next = var_Undef;
    Heap<VarOrderLt>& order_heap = glucose_restart ? order_heap_glue_r : order_heap_no_r;

    // Random decision:
    /*if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }*/

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty())
            return lit_Undef;
        else
            next = order_heap.removeMin();

    return mkLit(next, polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    // Trying to reduce proof size.
    add_oc.clear();
    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        // For binary clauses, we don't rearrange literals in propagate(), so check and make sure the first is an implied lit.
        if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        bool migrate_bin = false;
        bool otf_simp = !drup_file || (c.size() < 10 && (!c.learnt() || c.mark() == CORE));
        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (otf_simp && j >= 2  // For now, should use only "premise_bin" if printing proof.
                  && ((!drup_file && (premise[toInt(~q)] == ~c[0] || premise[toInt(c[0])] == q
                                   || premise[toInt(~q)] == ~c[1] || premise[toInt(c[1])] == q))
                      || premise_bin[toInt(~q)] == ~c[0] || premise_bin[toInt(c[0])] == q
                      || premise_bin[toInt(~q)] == ~c[1] || premise_bin[toInt(c[1])] == q)){
                if (drup_file && add_oc.size() == 0)
                    for (int k = 0; k < c.size(); k++)
                        add_oc.push(c[k]);

                lit_elim++;
                c[j--] = c.last();
                c.shrink(1); // FIXME: fix (statistical) memory leak.
                if (c.learnt()) learnts_literals--;
                else            clauses_literals--;

                if (c.size() == 2)
                    migrate_bin = true;
            }else if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()){
#ifdef EXTRA_VAR_ACT_BUMP
                    if (reason(var(q)) != CRef_Undef && ca[reason(var(q))].learnt())
                        add_tmp.push(q);
#endif
                    pathC++;
                }else
                    out_learnt.push(q);
            }
        }

        if (drup_file && add_oc.size() != 0){
            drup('a', c, drup_file);
            drup('d', add_oc, drup_file);
            add_oc.clear(); }

        // Update LBD if improved.
        if (c.learnt() && c.mark() != CORE && !migrate_bin){
            int lbd = computeLBD(c);
            if (lbd < c.lbd()){
                if (c.lbd() <= 30) c.removable(false); // Protect once from reduction.
                c.set_lbd(lbd);
                if (lbd <= core_lbd_cut){
                    learnts_core.push(confl);
                    c.mark(CORE);
                }else if (lbd <= 6 && c.mark() == LOCAL){
                    // Bug: 'cr' may already be in 'learnts_tier2', e.g., if 'cr' was demoted from TIER2
                    // to LOCAL previously and if that 'cr' is not cleaned from 'learnts_tier2' yet.
                    learnts_tier2.push(confl);
                    c.mark(TIER2); }
            }

            if (c.mark() == TIER2)
                c.touched() = conflicts;
            else if (c.mark() == LOCAL)
                claBumpActivity(c);
        }

        if (migrate_bin){
            assert(c.size() == 2); assert(!c.learnt() || c.mark() == CORE);
            assert(p == lit_Undef || value(c[0]) == l_True);

            static vec<Lit> bin_tmp(2);
            bin_tmp[0] = c[0]; bin_tmp[1] = c[1];

            bool learnt = c.learnt();  // We need a copy, as 'alloc' may invalidate the 'c' reference.
            CRef cr = ca.alloc(bin_tmp, learnt);
            if (p != lit_Undef)
                vardata[var(bin_tmp[0])].reason = cr;

            if (learnt){
                learnts_core.push(cr);
                ca[cr].mark(CORE);
                ca[cr].set_lbd(1);
            }else
                clauses.push(cr);
            // attachClause(cr)
            watches_bin[~bin_tmp[0]].push(Watcher(cr, bin_tmp[1]));
            watches_bin[~bin_tmp[1]].push(Watcher(cr, bin_tmp[0]));
            // removeClause(confl) without detachClause(confl)
            ca[confl].mark(1);
            ca.free(confl);
            // detachClause(confl)
            watches.smudge(~bin_tmp[0]);
            watches.smudge(~bin_tmp[1]);
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = c.size() == 2 ? 0 : 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    out_lbd = computeLBD(out_learnt);
    if (out_lbd <= 6 && out_learnt.size() <= 30) // Try further minimization?
        if (binResMinimize(out_learnt))
            out_lbd = computeLBD(out_learnt); // Recompute LBD if minimized.

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

#ifdef EXTRA_VAR_ACT_BUMP
    if (add_tmp.size() > 0){
        for (int i = 0; i< add_tmp.size(); i++)
            if (ca[reason(var(add_tmp[i]))].lbd() < out_lbd)
                varBumpActivity(var(add_tmp[i]));
        add_tmp.clear(); }
#endif
}


// Try further learnt clause minimization by means of binary clause resolution.
bool Solver::binResMinimize(vec<Lit>& out_learnt)
{
    // Preparation: remember which false variables we have in 'out_learnt'.
    counter++;
    for (int i = 1; i < out_learnt.size(); i++)
        seen2[var(out_learnt[i])] = counter;

    // Get the list of binary clauses containing 'out_learnt[0]'.
    const vec<Watcher>& ws = watches_bin[~out_learnt[0]];

    int to_remove = 0;
    for (int i = 0; i < ws.size(); i++){
        Lit the_other = ws[i].blocker;
        // Does 'the_other' appear negatively in 'out_learnt'?
        if (seen2[var(the_other)] == counter && value(the_other) == l_True){
            to_remove++;
            seen2[var(the_other)] = counter - 1; // Remember to remove this variable.
        }
    }

    // Shrink.
    if (to_remove > 0){
        int last = out_learnt.size() - 1;
        for (int i = 1; i < out_learnt.size() - to_remove; i++)
            if (seen2[var(out_learnt[i])] != counter)
                out_learnt[i--] = out_learnt[last--];
        out_learnt.shrink(to_remove);
    }
    return to_remove != 0;
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

        // Special handling for binary clauses like in 'analyze()'.
        if (c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = c.size() == 2 ? 0 : 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from, Lit dom)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);

    dominator[var(p)] = dom == lit_Undef ? p : dom;
}

void Solver::updatePremise(Lit p, Lit prem_p) {
    assert(prem_p != lit_Undef);
    assert(!drup_file);  // NO DRUP

    Lit old_prem;
    if ((old_prem = premise    [toInt(p)]) == prem_p
     && (old_prem = premise_bin[toInt(p)]) == prem_p)
        return;

    // Rationale: if p is implied by both q and ~q, then p is true.
    if (old_prem                 == ~prem_p
     || old_prem                 == ~premise[toInt(prem_p)]
     || premise[toInt(old_prem)] == ~prem_p
     || premise[toInt(old_prem)] == ~premise[toInt(prem_p)]){
        facts.push(p);
        if (decisionLevel() != 0) one_sided_lits++;
    }
/*
    Lit prem_not_p;
    // Rationale: if q implies both ~p and p, then ~q must be true.
    if ((prem_not_p = premise[toInt(~p)]) == prem_p || prem_not_p == old_prem
     || (prem_not_p = premise_bin[toInt(~p)]) == prem_p || prem_not_p == old_prem){
        facts.push(~prem_not_p);
        failed_lits++; }
*/
    premise[toInt(p)] = prem_p;
}

bool Solver::propagateFacts()
{
    assert(decisionLevel() == 0);
    assert(facts.size() == 0 || !drup_file);

    for (int i = 0; i < facts.size(); i++){
        if (value(facts[i]) == l_False)
            return false;
        else if (value(facts[i]) == l_Undef){
            int trail_sz = trail.size();
            uncheckedEnqueue(facts[i]);
            facts_enqueued++;

            if (propagate() != CRef_Undef)
                return false;
            probed_vars += trail.size() - trail_sz;
        }
    }
    facts.clear();

    return true;
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate(bool otf_probing)
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    Lit     dec = decisionLevel() == 0 ? lit_Undef : trail[trail_lim.last()];
    watches.cleanAll();
    watches_bin.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        Lit far_dom = lit_Undef;
        if (otf_probing)
            if (p == dec) far_dom = p;
            else if (level(var(premise[toInt(p)])) == decisionLevel())
                far_dom = premise[toInt(p)];

        vec<Watcher>& ws_bin = watches_bin[p];  // Propagate binary clauses first.
        for (int k = 0; k < ws_bin.size(); k++){
            Lit the_other = ws_bin[k].blocker;
            if (value(the_other) == l_False){
                confl = ws_bin[k].cref;
#ifdef LOOSE_PROP_STAT
                return confl;
#else
                goto ExitProp;
#endif
            }else if (value(the_other) == l_Undef){
                uncheckedEnqueue(the_other, ws_bin[k].cref, far_dom);
                if (far_dom != lit_Undef)
                    updatePremise(the_other, far_dom);
            }
            premise_bin[toInt(the_other)] = p;
        }

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            Lit dom = far_dom;
            // Look for new watch:
            for (int k = 2; k < c.size(); k++){
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

                if (dom != lit_Undef && level(var(c[k])) != 0 && ~c[k] != dom && dominator[var(c[k])] != dom)
                    dom = lit_Undef;
            }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else{
                uncheckedEnqueue(first, cr, dom);

                if (dom != lit_Undef)
                    updatePremise(first, dom);
            }

        NextClause:;
        }
        ws.shrink(i - j);
    }

ExitProp:;
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) const { return ca[x].activity() < ca[y].activity(); }
};
void Solver::reduceDB()
{
    int     i, j;
    sort(learnts_local, reduceDB_lt(ca));

    int limit = learnts_local.size() / 2;
    for (i = j = 0; i < learnts_local.size(); i++){
        Clause& c = ca[learnts_local[i]];
        if (c.mark() == LOCAL)
            if (c.removable() && !locked(c) && i < limit)
                removeClause(learnts_local[i]);
            else{
                if (!c.removable()) limit++;
                c.removable(true);
                learnts_local[j++] = learnts_local[i]; }
    }
    learnts_local.shrink(i - j);

    checkGarbage();
}
void Solver::reduceDB_Tier2()
{
    int i, j;
    for (i = j = 0; i < learnts_tier2.size(); i++){
        Clause& c = ca[learnts_tier2[i]];
        if (c.mark() == TIER2)
            if (!locked(c) && c.touched() + 30000 < conflicts){
                learnts_local.push(learnts_tier2[i]);
                c.mark(LOCAL);
                //c.removable(true);
                c.activity() = 0;
                claBumpActivity(c);
            }else
                learnts_tier2[j++] = learnts_tier2[i];
    }
    learnts_tier2.shrink(i - j);
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
        /* Just for future reference.
        if (value(c[0]) != l_Undef || value(c[1]) != l_Undef){  // Implies satisfied.
            removeClause(cs[i]);
            goto NextClause; }

        for (k = l = 2; k < c.size(); k++)
            if (value(c[k]) == l_True){
                removeClause(cs[i]);
                goto NextClause;
            }else if (value(c[k]) == l_Undef){
                if (premise[toInt(~c[k])] == ~c[0] || premise[toInt(c[0])] == c[k]
                 || premise[toInt(~c[k])] == ~c[1] || premise[toInt(c[1])] == c[k]
                 || premise_bin[toInt(~c[k])] == ~c[0] || premise_bin[toInt(c[0])] == c[k]
                 || premise_bin[toInt(~c[k])] == ~c[1] || premise_bin[toInt(c[1])] == c[k]){
                    lit_elim2++;
                }else
                    c[l++] = c[k];
            }
        c.shrink(k - l); // FIXME: fix (statistical) memory leak.
        if (c.learnt()) learnts_literals -= (k - l);
        else            clauses_literals -= (k - l);

        cs[j++] = cs[i];
    NextClause:;
        */
    }
    cs.shrink(i - j);
}

void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);

    order_heap_no_r  .build(vs);
    order_heap_glue_r.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify(bool do_stamping)
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    safeRemoveSatisfiedCompact(learnts_core, CORE);
    safeRemoveSatisfiedCompact(learnts_tier2, TIER2);
    safeRemoveSatisfiedCompact(learnts_local, LOCAL);
    if (remove_satisfied)        // Can be turned off.
        safeRemoveSatisfiedCompact(clauses, 0);

    if (do_stamping)
        ok = stampAll(true);

    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return ok;
}

// TODO: needs clean up.
void Solver::safeRemoveSatisfiedCompact(vec<CRef>& cs, unsigned valid_mark)
{
    if (cs.size() == 0) return;
    bool learnt = ca[cs[0]].learnt();

    // Trying to reduce proof size.
    bool otf_simp_base = !drup_file || !learnt || valid_mark == CORE;

    int i, j, k, l;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (c.mark() != valid_mark) continue;

        if (value(c[0]) != l_Undef || value(c[1]) != l_Undef){  // Implies satisfied.
            removeClause(cs[i]);
            continue; }

        if (drup_file){ // Remember the original clause before attempting to modify it.
            add_oc.clear();
            for (int i = 0; i < c.size(); i++) add_oc.push(c[i]); }

        // Also remove false literals and do on-the-fly probing.
        for (k = l = 2; k < c.size(); k++)
            if (value(c[k]) == l_True){
                removeClause(cs[i], true /* skip drup */);
                drup('d', add_oc, drup_file);
                goto NextClause;
            }else if (value(c[k]) == l_Undef){
                bool otf_simp = otf_simp_base && (!drup_file || c.size() < 10);
                if (otf_simp  // For now, should use only "premise_bin" if printing proof.
                        && ((!drup_file && (premise[toInt(~c[k])] == ~c[0] || premise[toInt(c[0])] == c[k]
                                         || premise[toInt(~c[k])] == ~c[1] || premise[toInt(c[1])] == c[k]))
                            || premise_bin[toInt(~c[k])] == ~c[0] || premise_bin[toInt(c[0])] == c[k]
                            || premise_bin[toInt(~c[k])] == ~c[1] || premise_bin[toInt(c[1])] == c[k]))
                    lit_elim3++;
                else
                    c[l++] = c[k];
            }

        // If became binary, we also need to migrate watchers. The easiest way is to allocate a new binary.
        if (l == 2 && k != 2){
            assert(add_tmp.size() == 0);
            // We need copies, as 'alloc' may invalidate the 'c' reference.
            int lbd = c.lbd();
            add_tmp.push(c[0]); add_tmp.push(c[1]);
            CRef cr = ca.alloc(add_tmp, learnt);
            add_tmp.clear();
            if (learnt){
                if (valid_mark != CORE) learnts_core.push(cr);
                ca[cr].mark(CORE);
                ca[cr].set_lbd(lbd > 2 ? 1 : lbd); }
            attachClause(cr);
            removeClause(cs[i], true /* skip drup */);
            // TODO: probably we can skip this if "(learnt && valid_mark != CORE)".
            cs[j++] = cr; // Should be after 'removeClause' because 'i' may be equal to 'j'.

            drup('a', ca[cr], drup_file);
            drup('d', add_oc, drup_file);
            goto NextClause;
        }

        if (k != l){  // Modified?
            c.shrink(k - l); // FIXME: fix (statistical) memory leak.
            if (learnt) learnts_literals -= (k - l);
            else        clauses_literals -= (k - l);

            drup('a', c, drup_file);
            drup('d', add_oc, drup_file);
        }
        cs[j++] = cs[i];
NextClause:;
    }
    cs.shrink(i - j);
}

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int& nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         lbd;
    vec<Lit>    learnt_clause;
    bool        cached = false;
    starts++;

    bool otf_probing = !drup_file && conflicts >= 50000 && starts % 10 == 0;
    for (;;){
        CRef confl = propagate(otf_probing);
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; nof_conflicts--;
            if (conflicts == 100000 && learnts_core.size() < 100) core_lbd_cut = 5;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level, lbd);
            cancelUntil(backtrack_level);

            lbd--;
            if (glucose_restart){
                conflicts_glue++;
                lbd_queue.push(lbd);
                global_lbd_sum += (lbd > 50 ? 50 : lbd);
                cached = false; }

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                ca[cr].set_lbd(lbd);
                if (lbd <= core_lbd_cut){
                    learnts_core.push(cr);
                    ca[cr].mark(CORE);
                }else if (lbd <= 6){
                    learnts_tier2.push(cr);
                    ca[cr].mark(TIER2);
                    ca[cr].touched() = conflicts;
                }else{
                    learnts_local.push(cr);
                    claBumpActivity(ca[cr]); }
                attachClause(cr);
                uncheckedEnqueue(learnt_clause[0], cr);
            }
            if (drup_file){
#ifdef BIN_DRUP
                binDRUP('a', learnt_clause, drup_file);
#else
                for (int i = 0; i < learnt_clause.size(); i++)
                    fprintf(drup_file, "%i ", (var(learnt_clause[i]) + 1) * (-2 * sign(learnt_clause[i]) + 1));
                fprintf(drup_file, "0\n");
#endif
            }

            varDecayActivity();
            claDecayActivity();

            /*if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }*/

        }else{
            // NO CONFLICT
            bool restart = false;
            if (!glucose_restart)
                restart = nof_conflicts <= 0;
            else if (!cached){
                double K = nof_conflicts > 0 ? 0.8 : 0.9;
                restart = lbd_queue.full() && (lbd_queue.avg() * K > global_lbd_sum / conflicts_glue);
                cached = true;
            }
            if (restart /* sometimes stalls || facts.size() != 0*/ /*|| !withinBudget()*/){
                lbd_queue.clear();
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && (!simplify(true) || !propagateFacts()))
                return l_False;

            if (conflicts >= next_T2_reduce){
                next_T2_reduce = conflicts + 10000;
                reduceDB_Tier2(); }
            if (conflicts >= next_L_reduce){
                next_L_reduce = conflicts + 15000;
                reduceDB(); }

            Lit next = lit_Undef;
            /*while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef)*/{
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("c ============================[ Search Statistics ]==============================\n");
        printf("c | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("c |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("c ===============================================================================\n");
    }

    add_tmp.clear();

    glucose_restart = true;
    int init = 10000;
    while (status == l_Undef && init > 0 /*&& withinBudget()*/)
       status = search(init);
    glucose_restart = false;

    // Search:
    int phase_allotment = 100;
    for (;;){
        int weighted = glucose_restart ? phase_allotment * 2 : phase_allotment;
        fflush(stdout);

        while (status == l_Undef && weighted > 0 /*&& withinBudget()*/)
            status = search(weighted);
        if (status != l_Undef /*|| !withinBudget()*/)
            break; // Should break here for correctness in incremental SAT solving.

        glucose_restart = !glucose_restart;
        if (!glucose_restart)
            phase_allotment += phase_allotment / 10;
    }

    if (verbosity >= 1)
        printf("c ===============================================================================\n");

#ifdef BIN_DRUP
    if (drup_file && status == l_False) binDRUP_flush(drup_file);
#endif

    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("c Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    watches_bin.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            vec<Watcher>& ws_bin = watches_bin[p];
            for (int j = 0; j < ws_bin.size(); j++)
                ca.reloc(ws_bin[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    // TODO: investigate if not every call needs to be "safeReloc()".
    safeReloc(to, learnts_core, CORE);
    safeReloc(to, learnts_tier2, TIER2);
    safeReloc(to, learnts_local, LOCAL);

    // All original:
    //
    safeReloc(to, clauses, 0);
}


void Solver::safeReloc(ClauseAllocator& to, vec<CRef>& cs, unsigned valid_mark) {
    int i, j;
    for (i = j = 0; i < cs.size(); i++)
        if (ca[cs[i]].mark() == valid_mark){
            ca.reloc(cs[i], to);
            cs[j++] = cs[i]; }
    cs.shrink(i - j);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}


inline int gcd(int a, int b) {
    int tmp;
    if (a < b) tmp = a, a = b, b = tmp;
    while (b) tmp = b, b = a % b, a = tmp;
    return a;
}

bool Solver::stampAll(bool use_bin_learnts)
{
    // Initialization.
    int stamp_time = 0;
    int nLits = 2*nVars();
    for (int i = 0; i < nVars(); i++){
        int m = i*2, n = i*2 + 1;
        discovered[m] = discovered[n] = finished[m] = finished[n] = observed[m] = observed[n] = 0;
        root[m] = root[n] = parent[m] = parent[n] = lit_Undef;
        flag[m] = flag[n] = 0; }

    for (int roots_only = 1; roots_only >= 0; roots_only--){
        int l = irand(random_seed, nLits);
        int l_inc = irand(random_seed, nLits-1) + 1; // Avoid 0 but ensure less than 'nLits'.
        while (gcd(nLits, l_inc) > 1)
            if (++l_inc == nLits) l_inc = 1;

        int first = l;
        do{
            Lit p = toLit(l);
            if (value(p) == l_Undef && !discovered[toInt(p)] &&
                    (!roots_only || isRoot(p, use_bin_learnts)) &&
                    implExistsByBin(p, use_bin_learnts)){
                stamp_time = stamp(p, stamp_time, use_bin_learnts);

                if (!ok || propagate() != CRef_Undef)
                    return ok = false;
            }

            // Compute next literal to look at.
            l += l_inc;
            if (l >= nLits) l -= nLits;

        }while(l != first);
    }

    return true;
}

int Solver::stamp(Lit p, int stamp_time, bool use_bin_learnts)
{
    assert(value(p) == l_Undef && !discovered[toInt(p)] && !finished[toInt(p)]);
    assert(rec_stack.size() == 0 && scc.size() == 0);

    int start_stamp = 0;
    rec_stack.push(Frame(Frame::START, p, lit_Undef, 0));

    while (rec_stack.size()){
        const Frame f = rec_stack.last(); rec_stack.pop();
        int i_curr = toInt(f.curr);
        int i_next = toInt(f.next);

        if (f.type == Frame::START){
            if (discovered[i_curr]){
                observed[i_curr] = stamp_time;
                continue; }

            assert(!finished[i_curr]);
            discovered[i_curr] = observed[i_curr] = ++stamp_time;

            if (start_stamp == 0){
                start_stamp = stamp_time;
                root[i_curr] = f.curr;
                assert(parent[i_curr] == lit_Undef); }
            rec_stack.push(Frame(Frame::CLOSE, f.curr, lit_Undef, 0));

            assert(!flag[i_curr]);
            flag[i_curr] = 1;
            scc.push(f.curr);

            for (int undiscovered = 0; undiscovered <= 1; undiscovered++){
                int prev_top = rec_stack.size();
                analyze_toclear.clear();

                const vec<Watcher>& ws = watches_bin[f.curr];
                for (int k = 0; k < ws.size(); k++){
                    Lit the_other = ws[k].blocker;

                    if (value(the_other) == l_Undef
                     && !seen[toInt(the_other)]
                     && undiscovered == !discovered[toInt(the_other)])
//                     && (use_bin_learnts || !ca[ws[k].cref].learnt()))
                    {
                        seen[toInt(the_other)] = 1;
                        analyze_toclear.push(the_other);

                        rec_stack.push(Frame(Frame::ENTER, f.curr, the_other, 0));
                        //rec_stack.push(Frame(Frame::ENTER, f.curr, the_other, ca[ws[k].cref].learnt()));
                    }
                }
                for (int k = 0; k < analyze_toclear.size(); k++) seen[toInt(analyze_toclear[k])] = 0;

                // Now randomize child nodes to visit by shuffling pushed stack entries.
                int stacked = rec_stack.size() - prev_top;
                for (int i = 0; i < stacked - 1; i++){
                    int j = i + irand(random_seed, stacked - i); // i <= j < stacked
                    if (i != j){
                        Frame tmp = rec_stack[prev_top + i];
                        rec_stack[prev_top + i] = rec_stack[prev_top + j];
                        rec_stack[prev_top + j] = tmp; }
                }
            }

        }else if (f.type == Frame::ENTER){
            rec_stack.push(Frame(Frame::RETURN, f.curr, f.next, f.learnt));

            int neg_observed = observed[toInt(~f.next)];
            if (start_stamp <= neg_observed){ // Failed literal?
                Lit failed;
                for (failed = f.curr;
                     discovered[toInt(failed)] > neg_observed;
                     failed = parent[toInt(failed)])
                    assert(failed != lit_Undef);

                if (drup_file && value(~failed) != l_True){
#ifdef BIN_DRUP
                    assert(add_tmp.size() == 0);
                    add_tmp.push(~failed);
                    binDRUP('a', add_tmp, drup_file);
                    add_tmp.clear();
#else
                    fprintf(drup_file, "%i 0\n", (var(~failed) + 1) * (-2 * sign(~failed) + 1));
#endif
                }

                if (!(ok = enqueue(~failed)))
                    return -1; // Who cares what?

                if (discovered[toInt(~f.next)] && !finished[toInt(~f.next)]){
                    rec_stack.pop(); // Skip this edge after a failed literal.
                    continue; }
            }

            if (!discovered[i_next]){
                parent[i_next] = f.curr;
                root[i_next] = p;
                rec_stack.push(Frame(Frame::START, f.next, lit_Undef, 0)); }

        }else if (f.type == Frame::RETURN){
            if (!finished[i_next] && discovered[i_next] < discovered[i_curr]){
                discovered[i_curr] = discovered[i_next];
                flag[i_curr] = 0;
            }
            observed[i_next] = stamp_time;

        }else if (f.type == Frame::CLOSE){
            if (flag[i_curr]){
                stamp_time++;
                int curr_discovered = discovered[i_curr];
                Lit q;
                do{
                    q = scc.last(); scc.pop();
                    flag      [toInt(q)] = 0;
                    discovered[toInt(q)] = curr_discovered;
                    finished  [toInt(q)] = stamp_time;
                }while (q != f.curr);
            }

        }else assert(false);
    }

    return stamp_time;
}

bool Solver::implExistsByBin(Lit p, bool use_bin_learnts) const {
    assert(value(p) == l_Undef);

    const vec<Watcher>& ws = watches_bin[p];
    for (int i = 0; i < ws.size(); i++){
        Lit the_other = ws[i].blocker;
        assert(value(the_other) != l_False); // Propagate then.

        if (value(the_other) != l_True && !discovered[toInt(the_other)])
            if (use_bin_learnts || !ca[ws[i].cref].learnt())
                return true;
    }
    return false;
}

bool Solver::isRoot(Lit p, bool use_bin_learnts) const { return !implExistsByBin(~p, use_bin_learnts); }
