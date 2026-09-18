#ifndef MOSER_LOWER_SIMPLEX_H
#define MOSER_LOWER_SIMPLEX_H

#include <math.h>
#include <string.h>

/* Untrusted maximization of a*w - sum penalty*|g*w| on the probability simplex.
   Start at the best vertex; use Bland's rule and a bounded pivot count. */
#define MIX_MEMBERS 24
#define MIX_AXES 78
#define MIX_COLUMNS (MIX_MEMBERS + 3*MIX_AXES)
#define MIX_ROWS (2*MIX_AXES + 1)
#define MIX_PIVOTS 256

typedef struct {
    double table[MIX_ROWS][MIX_COLUMNS+1], reduced[MIX_COLUMNS];
    int basis[MIX_ROWS];
} MixTableau;

static void mix_pivot(MixTableau *lp, int rows, int columns, int row, int column) {
    double pivot = lp->table[row][column];
    for (int j = 0; j <= columns; ++j) lp->table[row][j] /= pivot;
    for (int i = 0; i < rows; ++i) {
        if (i == row) continue;
        double factor = lp->table[i][column];
        if (factor == 0) continue;
        for (int j = 0; j <= columns; ++j)
            lp->table[i][j] -= factor * lp->table[row][j];
        lp->table[i][column] = 0;
    }
    lp->basis[row] = column;
}

static int mix_simplex(int members, int axes, const double intercept[MIX_MEMBERS],
                       double gradient[MIX_MEMBERS][MIX_AXES],
                       const double penalty[MIX_AXES],
                       double weight[MIX_MEMBERS], unsigned *pivots) {
    if (members < 1 || members > MIX_MEMBERS || axes < 0 || axes > MIX_AXES) return 0;
    MixTableau lp;
    int columns = members + 3*axes, rows = 2*axes + 1;
    for (int i = 0; i < rows; ++i)
        memset(lp.table[i], 0, (size_t)(columns+1)*sizeof(double));
    for (int j = 0; j < axes; ++j) {
        for (int k = 0; k < members; ++k) {
            lp.table[j][k] = gradient[k][j];
            lp.table[axes+j][k] = -gradient[k][j];
        }
        lp.table[j][members+j] = lp.table[axes+j][members+j] = -1;
        lp.table[j][members+axes+j] = lp.table[axes+j][members+2*axes+j] = 1;
        lp.basis[j] = members+axes+j;
        lp.basis[axes+j] = members+2*axes+j;
    }
    int best = 0;
    double best_value = -INFINITY;
    for (int k = 0; k < members; ++k) {
        lp.table[2*axes][k] = 1;
        double value = intercept[k];
        for (int j = 0; j < axes; ++j) value -= penalty[j] * fabs(gradient[k][j]);
        if (value > best_value) { best_value = value; best = k; }
    }
    lp.table[2*axes][columns] = 1;
    mix_pivot(&lp, rows, columns, 2*axes, best);
    for (int j = 0; j < axes; ++j) {
        int row = lp.table[j][columns] < 0 ? j : axes+j;
        if (lp.table[row][columns] < 0) mix_pivot(&lp, rows, columns, row, members+j);
    }
    for (int i = 0; i < rows; ++i)
        if (!isfinite(lp.table[i][columns]) || lp.table[i][columns] < -1e-9) return 0;
    for (int j = 0; j < columns; ++j)
        lp.reduced[j] = j < members ? intercept[j] :
            (j < members+axes ? -penalty[j-members] : 0);
    for (int i = 0; i < rows; ++i) {
        int basic = lp.basis[i];
        double cost = basic < members ? intercept[basic] :
            (basic < members+axes ? -penalty[basic-members] : 0);
        for (int j = 0; j < columns; ++j) lp.reduced[j] -= cost * lp.table[i][j];
    }
    int limited = 0;
    for (int iteration = 0; iteration < MIX_PIVOTS; ++iteration) {
        int enter = -1, leave = -1;
        for (int j = 0; j < columns; ++j)
            if (lp.reduced[j] > 1e-11) { enter = j; break; }
        if (enter < 0) break;
        double ratio = INFINITY;
        for (int i = 0; i < rows; ++i) {
            if (lp.table[i][enter] <= 1e-11) continue;
            double value = lp.table[i][columns] / lp.table[i][enter];
            if (value < ratio-1e-13 ||
                (value <= ratio+1e-13 && (leave < 0 || lp.basis[i] < lp.basis[leave]))) {
                ratio = value; leave = i;
            }
        }
        if (leave < 0) return 0;
        mix_pivot(&lp, rows, columns, leave, enter);
        double cost = lp.reduced[enter];
        for (int j = 0; j < columns; ++j) lp.reduced[j] -= cost * lp.table[leave][j];
        lp.reduced[enter] = 0;
        ++*pivots;
        if (iteration+1 == MIX_PIVOTS) limited = 1;
    }
    memset(weight, 0, (size_t)members*sizeof(double));
    for (int i = 0; i < rows; ++i)
        if (lp.basis[i] < members && lp.table[i][columns] > 0)
            weight[lp.basis[i]] = lp.table[i][columns];
    double total = 0;
    for (int k = 0; k < members; ++k) total += weight[k];
    if (!isfinite(total) || total <= 1e-12) return 0;
    for (int k = 0; k < members; ++k) weight[k] /= total;
    /* 0: failed, 1: converged, 2: pivot limit. Every result is only a proposal. */
    return limited ? 2 : 1;
}

#endif
