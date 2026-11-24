Code for the Frobenius note above, inline because the discussion link policy rules out repository links. Prepared with Claude Code assistance on behalf of `DiamondJM`. `coset.patch` and `coset_frob.cpp` are derived from Edgar Costa's `ToricControlledReduction` (LGPL 2.1) and carry the same licence.

**Build and run.**
1. Check out `ToricControlledReduction` at commit `74cda9e`, apply `coset.patch`, copy `coset_frob.cpp` to `examples/`.
2. `./configure && make build/examples/coset_frob.exe build/examples/readfile.exe` (needs NTL, FLINT, GMP).
3. `python3 validate/validate.py <clone>` compares the pieces with the unpatched program on two curves.
4. `./run_coset.sh <clone> 67 0,0,2,0 N2` gives the pole-3 columns modulo $p^2$ (enough for the table); `./run_coset.sh <clone> 19 0,3,3,0 N3` gives all columns modulo $p^3$.
5. `python3 coset_analyze.py` prints the table, the trace checks and the test for powers of Frobenius.

**What the patch does.** A `dr` object can be restricted to the lattice points $w$ with prescribed residues of linear forms, here $c+d \bmod 2$ and $u \bmod 3$. Two objects are used. The invariant ring (all residues zero) supplies every Jacobian relation and every reduction matrix. The coset module supplies the cohomology basis and the final reduction to it. Frobenius of a coset monomial is reduced along directions of the invariant ring only, so every intermediate monomial stays in the coset. The last step, from pole order $p$ to pole order 1 at a coset point $u$ of the polytope, uses $6u$ written as a sum of six ring points and $(p-1)/6$ steps along each; this needs $p\equiv1\pmod 6$.

<details>
<summary><code>coset.patch</code>: patch for <code>dr.h</code>, to be applied at commit 74cda9e</summary>

````diff
diff --git a/dr.h b/dr.h
index 80c4c44..66c951b 100644
--- a/dr.h
+++ b/dr.h
@@ -417,6 +417,46 @@ class dr{
 
         void frob_matrix(Mat<R> &res, Vec<int64_t> N, int64_t method = DEFAULT_VECTOR_REDUCTION_METHOD);
 
+        /*
+         * COSET PATCH (not part of the upstream library)
+         *
+         * Restriction to one isotypic piece of a finite diagonal group action.
+         * The group is the dual of M/M', where M = ZZ^n is the exponent lattice and
+         * M' = {w : LA*w = 0 mod Lmod} is a sublattice containing supp(f).
+         * A dr object with restricted = true only keeps the lattice points w with
+         *      (LA * w)[i] = Lres[i] mod Lmod[i]   for all i.
+         *  - Lres = 0: the invariant ring S' (the "ring object"); all Jacobian relations
+         *    and all reduction matrices are computed here.
+         *  - Lres != 0: the S'-module S^c of one nontrivial coset (the "module object",
+         *    coset_module = true); only its basis, pi/rho and last_reduction are used.
+         * Set these fields before calling init().
+         */
+        bool restricted = false;
+        bool coset_module = false;
+        Mat<int64_t> LA;
+        Vec<int64_t> Lmod, Lres;
+        // v is an (n + 1)-tuple (d, w)
+        bool in_coset(const Vec<int64_t> &v) const
+        {
+            for(int64_t i = 0; i < LA.NumRows(); i++)
+            {
+                int64_t t = 0;
+                for(int64_t j = 0; j < n; j++)
+                    t += LA[i][j] * v[j + 1];
+                t = ((t - Lres[i]) % Lmod[i] + Lmod[i]) % Lmod[i];
+                if(t != 0)
+                    return false;
+            }
+            return true;
+        }
+        // called on the ring object; mod is the object of the coset (it may be the ring object itself)
+        // ex = exponent of M/M', we need p = 1 mod ex so that Frobenius preserves the cosets
+        // F \in mod.P_1 + mod.J_2 + ...
+        void frob_monomial_coset(Vec<R> &F, const Vec<int64_t> &w, int64_t N, dr<R> &mod, int64_t ex, int64_t method = DEFAULT_VECTOR_REDUCTION_METHOD);
+        // rows [start, end) of the list of basis elements of mod.basis_dr_X; res has one row per basis element
+        // and mod.dim_dr_Y columns (coordinates in mod.basis_dr_Y)
+        void frob_rows_coset(Mat<R> &res, Vec<int64_t> N, dr<R> &mod, int64_t ex, int64_t start, int64_t end, int64_t method = DEFAULT_VECTOR_REDUCTION_METHOD);
+
 
 
         /*
@@ -554,7 +594,9 @@ void dr<R>::init(const int64_t &p, const map< Vec<int64_t>, R, vi64less> &f, con
     {
         init_solve_and_cokernels();
         init_rho_and_pi_matrices();
-        init_inclusion_matrices();
+        // COSET PATCH: the inclusion J' -> S^c is applied in frob_monomial_coset
+        if(not coset_module)
+            init_inclusion_matrices();
         init_last_reduction();
         init_proj();
     }
@@ -582,9 +624,31 @@ void dr<R>::init_tuples()
             v[i] = fit->first[i + 1];
         fkeys.append(v);
     }
-    integral_points(tuple_list, tuple_int_list, AP, bP, fkeys, n + 2);
+    if(not restricted)
+        integral_points(tuple_list, tuple_int_list, AP, bP, fkeys, n + 2);
+    else
+    {
+        // COSET PATCH: keep only the points of the coset
+        Vec< Vec< Vec<int64_t> > > full_list, full_int_list;
+        integral_points(full_list, full_int_list, AP, bP, fkeys, n + 2);
+        coset_module = false;
+        for(i = 0; i < Lres.length(); i++)
+            if( Lres[i] % Lmod[i] != 0 )
+                coset_module = true;
+        tuple_list.SetLength(n + 2);
+        tuple_int_list.SetLength(n + 2);
+        for(int64_t d = 0; d < n + 2; d++)
+        {
+            for(i = 0; i < full_list[d].length(); i++)
+                if( in_coset(full_list[d][i]) )
+                    tuple_list[d].append(full_list[d][i]);
+            for(i = 0; i < full_int_list[d].length(); i++)
+                if( in_coset(full_int_list[d][i]) )
+                    tuple_int_list[d].append(full_int_list[d][i]);
+        }
+    }
 
-    assert_print(tuple_list[0].length(), ==, 1);
+    assert_print(tuple_list[0].length(), ==, (coset_module ? 0 : 1));
     assert_print(tuple_int_list[0].length(), ==, 0 );
 
     tuple_dict.SetLength(n + 2);
@@ -725,7 +789,8 @@ void dr<R>::init_solve_and_cokernels()
     for(i = 0; i < n + 2; i++)
     {
         cokernels_J_dimensions[i] = conv< long >( coeff(P, i) );
-        if(cokernels_J_dimensions[i] == 0)
+        // COSET PATCH: for a nontrivial coset S^c_0 = 0
+        if(cokernels_J_dimensions[i] == 0 and not (coset_module and i == 0))
         {
             this->max_pole = i - 1;
             break;
@@ -747,6 +812,13 @@ void dr<R>::init_solve_and_cokernels()
     solve_denom.SetLength(max_pole + 2);
     for(i =0; i <= max_pole + 1; i++)
     {
+        if(i == 0 and coset_module)
+        {
+            // COSET PATCH: S^c_0 = 0
+            solve_denom[0] = 1;
+            cokernels_J_basis[0].SetLength(0);
+            continue;
+        }
         if(i == max_pole + 1 and verbose > 1)
             cout << "Asserting that the hypersurface is non degenerate" << endl;
 
@@ -767,7 +839,19 @@ void dr<R>::init_solve_and_cokernels()
         {
             initB.SetLength(0);
         }
-        solve_system(B, solve_matrix[i], solve_denom[i], J, initB);
+        if( J.NumCols() == 0 )
+        {
+            // COSET PATCH: no relations in this degree (S^c_{i-1} = 0), J_i = P_i
+            B.SetLength(J.NumRows());
+            for(j = 0; j < J.NumRows(); j++)
+                B[j] = j;
+            solve_matrix[i].SetDims(J.NumRows(), J.NumRows());
+            for(j = 0; j < J.NumRows(); j++)
+                solve_matrix[i][j][j] = 1;
+            solve_denom[i] = 1;
+        }
+        else
+            solve_system(B, solve_matrix[i], solve_denom[i], J, initB);
         if(B.length() != cokernels_J_dimensions[i])
         {
             cout<<"dr::Something went wrong, perhaps the hypersurface is not nondegenerate..."<<endl;
@@ -847,14 +931,15 @@ void dr<R>::init_cokernels_I_basis()
         reverse_dict(cokernels_I_basis_dict[d], cokernels_I_basis[d]);
         cokernels_I_dimensions[d] = cokernels_I_basis[d].length();
         hodge_numbers[d - 1] = cokernels_I_basis[d].length();
-        if( hodge_numbers[d - 1] == 0 and 2*d <  n + 1 )
+        // COSET PATCH: an isotypic piece need not be Hodge symmetric
+        if( not restricted and hodge_numbers[d - 1] == 0 and 2*d <  n + 1 )
         {
             // hodge symmetry implies H^(w -d, d) = H^(d, w-d) = 0
             max_hi--;
             hodge_numbers[n - 1 - (d - 1)] = 0;
             cokernels_I_basis[n - d + 1].SetLength(0);
         }
-        if( 2*d >  n + 1) // d - 1 > (n - 1)- ( d - 1)
+        if( not restricted and 2*d >  n + 1) // d - 1 > (n - 1)- ( d - 1)
         {
             if(hodge_numbers[d - 1] != hodge_numbers[(n - 1) - (d -1)] )
             {
@@ -884,8 +969,9 @@ void dr<R>::init_cokernels_I_basis(int64_t d)
 {
     if(verbose > 2)
         cout<<"dr::init_cokernels_I_basis("<<d<<")"<<endl;
-    if(d == 1)
+    if(d == 1 or tuple_int_list[d].length() == 0 or tuple_list[d - 1].length() == 0)
     {
+        // COSET PATCH: also covers the degenerate cases S^*_d = 0 and S_{d-1} = 0
         cokernels_I_basis[d] = tuple_int_list[d];
     }
     else
@@ -2151,4 +2237,235 @@ void dr<R>::frob_monomial(Vec<R> &F, const Vec<int64_t> &w, int64_t N, int64_t m
 }
 
 
+/*
+ * COSET PATCH (not part of the upstream library)
+ * See the comments in the class declaration.
+ */
+template<typename R>
+void dr<R>::frob_rows_coset(Mat<R> &res, Vec<int64_t> N, dr<R> &mod, int64_t ex, int64_t start, int64_t end, int64_t method)
+{
+    assert_print( mod.max_pole, <=, N.length() );
+    int64_t i, m, pos, row;
+    res.kill();
+    res.SetDims( end - start, mod.dim_dr_Y );
+    pos = 0;
+    row = 0;
+    for(m = 1; m < mod.max_pole + 1; m++)
+    {
+        for(i = 0; i < mod.basis_dr_X[m].length(); i++, pos++)
+        {
+            if(pos < start or pos >= end)
+                continue;
+            if(verbose > 0)
+                cout<<"Computing Frob("<<mod.basis_dr_X[m][i]<<") m = "<<m<<" N = "<<N[m-1]<<endl;
+            frob_monomial_coset(res[row], mod.basis_dr_X[m][i], N[m - 1], mod, ex, method);
+            row++;
+        }
+    }
+}
+
+template<typename R>
+void dr<R>::frob_monomial_coset(Vec<R> &F, const Vec<int64_t> &w, int64_t N, dr<R> &mod, int64_t ex, int64_t method)
+{
+    int64_t i, j, k, m, e, end;
+    if(F.length() != mod.dim_dr_Y)
+        F.SetLength(mod.dim_dr_Y);
+    for(i = 0; i < mod.dim_dr_Y; i++)
+        F[i] = R(0);
+    if(N == 0)
+        return;
+
+    assert_print(p, !=, 0);
+    assert_print((p - 1) % ex, ==, 0);
+    assert_print(max_pole, <=, mod.max_pole);
+    assert( not coset_module );
+
+    init_f_frob_power(N - 1);
+    R fact = R(1);
+
+    map< Vec<int64_t>, Vec<R>, vi64less> H;
+    typename map< Vec<int64_t>, Vec<R>, vi64less>::const_iterator Hit;
+    typename map< Vec<int64_t>, Vec<R>, vi64less>::iterator Hnewit;
+    m = w[0];
+
+    for(e = m + N - 1; e > 0; e--)
+    {
+        map< Vec<int64_t>, Vec<R>, vi64less> Hnew;
+        if( verbose > 1 )
+            cout <<"\t e = "<< e << " keys = " << H.size() << endl;
+
+        //add terms of pole order e
+        if( e >= m )
+        {
+            j = e - m;
+            R Djm;
+            Djm = conv<R>( binomial(m + j - 1, m - 1));
+            if (j%2 != 0)
+                Djm = -Djm;
+            Djm *= conv<R>( binomial(m + N - 1, N -j - 1) );
+
+            typename map< Vec<int64_t>, R, vi64less >::const_iterator fjit;
+            for(fjit = f_frob_power[j].cbegin(); fjit != f_frob_power[j].cend(); fjit++)
+            {
+                if(fjit->second != 0)
+                {
+                    Vec<int64_t> monomial = w + fjit->first;
+                    Hit = H.find(monomial);
+                    if( Hit == H.end() )
+                        H[monomial].SetLength(dim_J, R(0));
+                    H[monomial][0] += Djm * fact * fjit->second;
+                }
+            }
+        }
+
+        end = (e > 1) ? p : p - 1;
+
+        for(i = 0; i < end; i++)
+            fact *= p*e - i - 1;
+
+        Vec<int64_t> shift;
+        if( e > m)
+            shift = w;
+        else
+            shift.SetLength(n + 1, int64_t(0));
+
+        for(Hit = H.cbegin();  Hit != H.end(); Hit++)
+        {
+            const Vec<int64_t> &u = Hit->first;
+            const Vec<R> &G = Hit->second;
+            assert_print(u[0], ==, e);
+            Vec<R> Gnew;
+            R den;
+            Vec<int64_t> final_dest;
+            if( e > 1 )
+            {
+                // a direction in the invariant ring: u - v stays in the coset
+                for(i = 0; i < tuple_list[1].length(); i++)
+                    if( min_P(u - shift - tuple_list[1][i]) <= e - shift[0] - 1)
+                        break;
+                if( i >= tuple_list[1].length() )
+                {
+                    cout << "couldn't find a v for u = "<<u<<endl;
+                    abort();
+                }
+                Vec<int64_t> &v = tuple_list[1][i];
+                Vec<int64_t> dest = p*u - end*v;
+                reduce_vector(Gnew, den, dest, v, end, G, method);
+                assert_print(den, ==, 1);
+                final_dest = u - v;
+                assert_print(p*final_dest, ==, dest);
+            }
+            else
+            {
+                // e = 1: x^(p u) = x^u * prod_l v_l^(k_l) with v_l in the invariant ring,
+                // where ex * u = sum of ex points of P'_1 and k_l = multiplicity * (p - 1)/ex
+                Vec<int64_t> x = ex * u;
+                Vec<int64_t> dirs;
+                for(int64_t lvl = ex; lvl >= 1; lvl--)
+                {
+                    for(i = 0; i < tuple_list[1].length(); i++)
+                        if( min_P(x - tuple_list[1][i]) <= lvl - 1)
+                            break;
+                    if( i >= tuple_list[1].length() )
+                    {
+                        cout << "couldn't decompose ex*u for u = "<<u<<endl;
+                        abort();
+                    }
+                    x = x - tuple_list[1][i];
+                    dirs.append(i);
+                }
+                for(i = 0; i < n + 1; i++)
+                    assert_print(x[i], ==, 0);
+
+                Vec<int64_t> rem = p*u;
+                Gnew = G;
+                for(k = 0; k < dirs.length(); k++)
+                {
+                    // merge the equal directions that follow each other
+                    int64_t mult = 1;
+                    while(k + 1 < dirs.length() and dirs[k + 1] == dirs[k])
+                    {
+                        mult++;
+                        k++;
+                    }
+                    Vec<int64_t> &v = tuple_list[1][dirs[k]];
+                    int64_t steps = mult * ((p - 1)/ex);
+                    Vec<int64_t> dest = rem - steps*v;
+                    Vec<R> Gtmp;
+                    reduce_vector(Gtmp, den, dest, v, steps, Gnew, method);
+                    assert_print(den, ==, 1);
+                    Gnew = Gtmp;
+                    rem = dest;
+                }
+                final_dest = u;
+                assert_print(final_dest, ==, rem);
+            }
+            if( not IsZero(Gnew) )
+            {
+                Hnewit = Hnew.find(final_dest);
+                if( Hnewit == Hnew.end())
+                    Hnew[final_dest] = Gnew;
+                else
+                    Hnewit->second += Gnew;
+            }
+        }
+        H.swap(Hnew);
+    }
+
+    assert_print(mod.last_reduction_den, ==, 1);
+
+    // u * (J'_0 + ... + J'_max_pole) --> mod.P_1 + ... + mod.P_{max_pole + 1}
+    Vec<int64_t> shift_rows, shift_columns;
+    shift_rows.SetLength(max_pole + 1);
+    shift_columns.SetLength(max_pole + 1);
+    int64_t total_columns = 0, total_rows = 0;
+    for(k = 0; k < max_pole + 1; k++)
+    {
+        shift_columns[k] = total_columns;
+        shift_rows[k] = total_rows;
+        total_columns += cokernels_J_dimensions[k];
+        total_rows += mod.tuple_list[k + 1].length();
+    }
+    for(Hit = H.cbegin(); Hit != H.cend(); Hit++)
+    {
+        const Vec<int64_t> &u = Hit->first;
+        const Vec<R> &G = Hit->second;
+        Vec<R> big;
+        big.SetLength(mod.last_reduction.NumCols(), R(0));
+        for(k = 0; k < max_pole + 1; k++)
+            for(j = 0; j < cokernels_J_dimensions[k]; j++)
+            {
+                typename map< Vec<int64_t>, int64_t, vi64less>::const_iterator it;
+                it = mod.tuple_dict[k + 1].find(u + cokernels_J_basis[k][j]);
+                if(it == mod.tuple_dict[k + 1].end())
+                {
+                    cout << "the product is not in the coset: u = "<<u<<" b = "<<cokernels_J_basis[k][j]<<endl;
+                    abort();
+                }
+                big[shift_rows[k] + it->second] += G[shift_columns[k] + j];
+            }
+        F += mod.last_reduction * big;
+    }
+
+    // F *= p^{n - 1}/ factorial(p * (m + N - 1) - 1)
+    R fact_padic;
+    int64_t val;
+    factorial_padic(fact_padic, val, p * (m + N - 1) - 1, p);
+    F *= inv(fact_padic);
+    if(n - 1 >= val)
+        F *= conv<R>(power_ZZ(p, n - 1 - val));
+    else
+    {
+        R ppower = conv<R>(power_ZZ(p, val - (n - 1)));
+        R q, r;
+        for(i = 0; i < F.length(); i++)
+        {
+            divrem_lift(q, r, F[i], ppower);
+            assert( IsZero(r) );
+            F[i] = q;
+        }
+    }
+}
+
+
 #endif
````

</details>

<details>
<summary><code>coset_frob.cpp</code>: driver, goes into <code>examples/</code></summary>

````cpp
// COSET PATCH driver (not part of the upstream library).
//
// Frobenius on one isotypic piece of the cohomology of a nondegenerate toric hypersurface
// with a finite diagonal symmetry group, to low p-adic precision.
//
// Usage:
//   coset_frob.exe input_file output_file "constraints" N_1,...,N_n [start end] [extra_precision] [verbose]
// where
//   - input_file has one line label:monomials:coefficients:A:b:p (as for readfile.exe)
//   - constraints = "a_1 ... a_n modulus residue; ..." keeps the exponents w with a.w = residue mod modulus
//   - N_m = number of terms of the Frobenius expansion used for the basis elements of pole order m
//     (0 = skip them); the column of a basis element of pole order m is then correct mod p^(N_m)
//   - [start, end) = range of basis elements to compute (default: all)
// Output (text): header lines, then one line per computed basis element:
//   row <index> <pole order> : coordinates of Frob(basis element) in the basis of the piece (mod p^precision)
#include <fstream>
#include <sstream>
#include <vector>
#include "hypersurface.h"

template<typename R>
int run(const int64_t p, const map< Vec<int64_t>, ZZ, vi64less> &f, const Mat<int64_t> &AP, const Vec<int64_t> &bP,
        const Mat<int64_t> &LA, const Vec<int64_t> &Lmod, const Vec<int64_t> &Lres, const Vec<int64_t> &N,
        int64_t start, int64_t end, int64_t ex, int64_t precision, int64_t verbose, ofstream &out)
{
    map< Vec<int64_t>, R, vi64less> fR = conv< map< Vec<int64_t>, R, vi64less> >(f);
    Vec<int64_t> zero;
    zero.SetLength(Lres.length(), 0);

    dr<R> ring, mod;
    ring.restricted = true; ring.LA = LA; ring.Lmod = Lmod; ring.Lres = zero;
    ring.init(p, fR, fR, AP, bP, verbose, false);
    bool trivial = true;
    for(int64_t i = 0; i < Lres.length(); i++)
        if(Lres[i] % Lmod[i] != 0)
            trivial = false;
    dr<R> *M = &ring;
    if(not trivial)
    {
        mod.restricted = true; mod.LA = LA; mod.Lmod = Lmod; mod.Lres = Lres;
        mod.init(p, fR, fR, AP, bP, verbose, false);
        M = &mod;
    }
    out << "p " << p << "\nprecision " << precision << "\nN " << N << "\n";
    out << "ring_dim_J " << ring.cokernels_J_dimensions << "\n";
    out << "piece_dim_J " << M->cokernels_J_dimensions << "\n";
    out << "piece_hodge " << M->hodge_numbers << "\n";
    out << "dim_dr_X " << M->dim_dr_X << " dim_dr_Y " << M->dim_dr_Y << "\n";
    // position of the X-basis inside the Y-basis
    out << "X_in_Y";
    {
        int64_t shiftY = 0;
        for(int64_t m = 1; m < M->max_pole + 1; m++)
        {
            for(int64_t i = 0; i < M->basis_dr_X[m].length(); i++)
                out << " " << shiftY + M->basis_dr_Y_dict[m][ M->basis_dr_X[m][i] ];
            shiftY += M->basis_dr_Y[m].length();
        }
        out << "\n";
    }
    out << "basis";
    for(int64_t m = 1; m < M->max_pole + 1; m++)
        for(int64_t i = 0; i < M->basis_dr_X[m].length(); i++)
            out << " " << M->basis_dr_X[m][i];
    out << "\n";
    out.flush();
    if(end < 0 or end > M->dim_dr_X)
        end = M->dim_dr_X;
    if(start >= end)
        return 0;

    Mat<R> rows;
    ring.frob_rows_coset(rows, N, *M, ex, start, end);
    Vec<int64_t> pole;
    for(int64_t m = 1; m < M->max_pole + 1; m++)
        for(int64_t i = 0; i < M->basis_dr_X[m].length(); i++)
            pole.append(m);
    for(int64_t i = 0; i < rows.NumRows(); i++)
    {
        out << "row " << start + i << " " << pole[start + i] << " :";
        for(int64_t j = 0; j < rows.NumCols(); j++)
            out << " " << rows[i][j];
        out << "\n";
    }
    out.flush();
    return 0;
}

int main(int argc, char **argv)
{
    if(argc < 5)
    {
        fprintf(stderr, "Usage: %s input output \"constraints\" N_1,..,N_n [start end] [extra_precision] [verbose]\n", argv[0]);
        return 1;
    }
    ifstream input(argv[1]);
    ofstream out(argv[2]);
    string line;
    getline(input, line);
    // label:monomials:coefficients:A:b:p
    int64_t p = 0;
    map< Vec<int64_t>, ZZ, vi64less> f;
    Mat<int64_t> AP, monomials;
    Vec<int64_t> bP;
    Vec<ZZ> coefficients;
    {
        stringstream ls(line);
        string s;
        for(int i = 0; i < 6; i++)
        {
            if(not getline(ls, s, ':'))
                throw_line("missing field");
            stringstream ss(s);
            if(i == 1) ss >>= monomials;
            if(i == 2) ss >>= coefficients;
            if(i == 3) ss >>= AP;
            if(i == 4) ss >>= bP;
            if(i == 5) ss >> p;
        }
        for(long i = 0; i < coefficients.length(); ++i)
            f[monomials[i]] = coefficients[i];
    }
    int64_t n = monomials.NumCols();

    // constraints
    Mat<int64_t> LA;
    Vec<int64_t> Lmod, Lres;
    int64_t ex = 1;
    {
        string cs(argv[3]);
        stringstream css(cs);
        string one;
        std::vector< std::vector<int64_t> > rows;
        while(getline(css, one, ';'))
        {
            stringstream os(one);
            std::vector<int64_t> r;
            int64_t t;
            while(os >> t) r.push_back(t);
            if(r.size() == 0) continue;
            if((int64_t) r.size() != n + 2) throw_line("bad constraint");
            rows.push_back(r);
        }
        LA.SetDims(rows.size(), n);
        Lmod.SetLength(rows.size());
        Lres.SetLength(rows.size());
        for(size_t i = 0; i < rows.size(); i++)
        {
            for(int64_t j = 0; j < n; j++) LA[i][j] = rows[i][j];
            Lmod[i] = rows[i][n];
            Lres[i] = rows[i][n + 1];
            ex = ex * Lmod[i] / GCD(ex, Lmod[i]);
        }
    }
    if((p - 1) % ex != 0)
    {
        cerr << "need p = 1 mod " << ex << endl;
        return 1;
    }

    Vec<int64_t> N;
    {
        string ns(argv[4]);
        stringstream nss(ns);
        string one;
        while(getline(nss, one, ','))
            N.append(atol(one.c_str()));
    }
    if(N.length() != n) throw_line("need n values of N");
    int64_t start = 0, end = -1, extra = 0, verbose = 0;
    if(argc > 6) { start = atol(argv[5]); end = atol(argv[6]); }
    if(argc > 7) extra = atol(argv[7]);
    if(argc > 8) verbose = atol(argv[8]);

    // working precision, as in working_precision(): the column of pole order m = k + 1 is wanted mod p^(N_k)
    int64_t precision = 1;
    for(int64_t k = 0; k < n; k++)
        if(N[k] > 0)
            precision = max(precision, N[k] + max(int64_t(0), valuation_of_factorial(p * (k + N[k]) - 1, p) - (n - 1)));
    precision += extra;

    ZZ modulus = power_ZZ(p, precision);
    cout << "p = " << p << " precision = " << precision << " ex = " << ex << " N = " << N << endl;
    if(NumBits(modulus) <= NTL_SP_NBITS)
    {
        zz_pPush push(conv<long>(modulus));
        return run<zz_p>(p, f, AP, bP, LA, Lmod, Lres, N, start, end, ex, precision, verbose, out);
    }
    else
    {
        ZZ_pPush push(modulus);
        return run<ZZ_p>(p, f, AP, bP, LA, Lmod, Lres, N, start, end, ex, precision, verbose, out);
    }
}
````

</details>

<details>
<summary><code>make_input.py</code>: input line for T: torus coordinates (b, c, d, u), polytope b + c + d + 2u ≤ 6</summary>

````python
"""Input line for ToricControlledReduction (Costa-Harvey-Kedlaya): the core threefold
T: u^3 + H(a,b,c,d) = 0 in P(1,1,1,1,2), chart a = 1, torus coordinates (b, c, d, u), scaled by 7."""
import sys
p = int(sys.argv[1])
f = {(0,0,0,0): 7, (6,0,0,0): 7, (1,0,0,0): 5, (5,0,0,0): 10,          # a^6, b^6, (5/7)a^5 b, (10/7) a b^5
     (0,6,0,0): 7, (0,0,6,0): 7, (0,5,1,0): 5, (0,1,5,0): 15,          # c^6, d^6, (5/7)c^5 d, (15/7) c d^5
     (1,1,1,0): 5, (1,3,1,0): 10,                                      # (5/7) a^3 b c d, (10/7) a b c^3 d
     (0,0,0,3): 7}                                                     # u^3
A = [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1],[-1,-1,-1,-2]]; b = [0,0,0,0,6]
fmt = lambda x: str(x).replace(' ', '').replace('(', '[').replace(')', ']')
print(f"core_p{p}:{fmt(list(f.keys()))}:{fmt(list(f.values()))}:{fmt(A)}:{fmt(b)}:{p}")
````

</details>

<details>
<summary><code>run_coset.sh</code>: runs the two σ-odd deck pieces at one prime</summary>

````bash
#!/bin/bash
# Frobenius on the two sigma-odd deck pieces of H^3(T) at one prime, with the patched library.
#   usage: run_coset.sh <dir of the patched ToricControlledReduction build> <p> <N_1,N_2,N_3,N_4> <tag>
# e.g.   run_coset.sh ~/ToricControlledReduction 67 0,0,2,0 N2     (pole-3 columns mod p^2)
#        run_coset.sh ~/ToricControlledReduction 19 0,3,3,0 N3     (all columns mod p^3)
# Build: clone edgarcosta/ToricControlledReduction (commit 74cda9e), `git apply coset.patch`,
# copy coset_frob.cpp to examples/, then ./configure && make build/examples/coset_frob.exe
set -e
here="$(cd "$(dirname "$0")" && pwd)"
B="$1/build/examples"; p=$2; N=$3; tag=$4
mkdir -p "$here/data"
python3 "$here/make_input.py" $p > "$here/data/in$p.txt"
for r in 1 2; do
  # exponents (b,c,d,u): c + d odd (sigma-odd), u = r mod 3 (deck character)
  "$B/coset_frob.exe" "$here/data/in$p.txt" "$here/data/c${r}_p${p}_${tag}.txt" "0 1 1 0 2 1; 0 0 0 1 3 $r" $N
done
````

</details>

<details>
<summary><code>coset_analyze.py</code>: slope-1 polynomials, factor degrees, trace checks, powers of Frobenius (python-flint 0.9)</summary>

````python
"""Analysis of the output of the patched ToricControlledReduction driver (coset_frob) for the
sigma-odd part of H^3(T), T: u^3 + H = 0, split by the deck character.

  piece 1 = exponents with c+d odd, u = 1 mod 3   Hodge (h30,h21,h12,h03) = (0,32,16,0)
  piece 2 = exponents with c+d odd, u = 2 mod 3   Hodge (0,16,32,0), dual to piece 1

Files data/c{r}_p{p}_N{k}.txt: 'row j m : v' = coordinates of Frob(basis element j, pole order m).
Columns of pole order 3 are computed mod p^2 (N2) or p^3 (N3); those of pole order 2 only in N3.

For each prime: the slope-1 polynomial of piece r mod p is the characteristic polynomial of the
(pole 3, pole 3) block of Frob/p.  By duality the slope-1 polynomial of piece 2 has the same
p-adic factor degrees as the slope-2 part of piece 1.
"""
import sys, os
from flint import nmod_mat, fmpz_mat
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data')
POINTCOUNT = {19: 133, 31: -155, 67: 134}        # trace on the sigma-odd part, from pointcount.py
# kmehltretter82's eigen-traces a + b*zeta on V_zeta (discussion 120, 2026-11-21); the sum over both pieces is 2a - b
EIGENTRACE = {19: (76, 19), 31: (-93, -31), 37: (-296, -185), 43: (215, 215), 61: (-61, -122)}

def load(r, p, tag):
    d = {}; rows = {}
    for line in open(os.path.join(D, f'c{r}_p{p}_{tag}.txt')):
        if line.startswith('row'):
            h, v = line.split(':'); _, i, m = h.split(); rows[int(i)] = (int(m), [int(x) for x in v.split()])
        else:
            k, _, v = line.strip().partition(' '); d[k] = v.strip()
    xin = [int(x) for x in d['X_in_Y'].split()]
    return d, rows, xin

def unit_poly(r, p, tag):
    d, rows, xin = load(r, p, tag)
    n = len(xin)
    idx3 = [j for j in range(n) if rows[j][0] == 3]
    xs = set(xin)
    assert all(x % p**2 == 0 for j in idx3 for c, x in enumerate(rows[j][1]) if c not in xs), 'not in H^3(T)'
    assert all(x % p == 0 for j in idx3 for x in rows[j][1]), 'pole-3 column not divisible by p'
    B = nmod_mat(len(idx3), len(idx3), [(rows[j][1][xin[i]] // p) % p for i in idx3 for j in idx3], p)
    return d['piece_hodge'], B.charpoly(), int(sum(B[i, i] for i in range(len(idx3))))

def subset_sums(ds):
    s = {0}
    for d in ds: s |= {x + d for x in s}
    return s

def main():
    primes = sorted({int(f.split('_p')[1].split('_')[0]) for f in os.listdir(D) if f.endswith('_N2.txt')})
    S1 = S2 = None
    print('p-adic factor degrees of the characteristic polynomial of Frobenius on piece 1 (48 = 16 + 32)')
    for p in primes:
        out = []; tot = 0
        for r in (1, 2):
            h, cp, tr = unit_poly(r, p, 'N2')
            fac = cp.factor()[1]
            assert int(cp[0]) != 0, 'not ordinary'
            sq = all(e == 1 for f, e in fac)
            out.append((sorted(f.degree() for f, e in fac for _ in range(e)), sq))
            tot += tr
        if out[0][1]: S1 = subset_sums(out[0][0]) if S1 is None else S1 & subset_sums(out[0][0])
        if out[1][1]: S2 = subset_sums(out[1][0]) if S2 is None else S2 & subset_sums(out[1][0])
        chk = ''
        if p in POINTCOUNT:
            chk = '   trace check vs point count: ' + ('OK' if (p*tot - POINTCOUNT[p]) % p**2 == 0 else 'MISMATCH')
        note = lambda o: '' if o[1] else ' (not squarefree mod p; not used)'
        print(f'  p = {p:3d}: slope 1: {out[0][0]}{note(out[0])}   slope 2: {out[1][0]}{note(out[1])}{chk}')
        print(f'           possible (slope-1 rank, slope-2 rank) of a sub-object so far: {sorted(S1)} x {sorted(S2)}')
    # full matrices mod p^3 where available
    for p in primes:
        if not os.path.exists(os.path.join(D, f'c1_p{p}_N3.txt')): continue
        tot = 0
        for r in (1, 2):
            d, rows, xin = load(r, p, 'N3'); n = len(xin); xs = set(xin)
            assert all(x % p**3 == 0 for j in range(n) for c, x in enumerate(rows[j][1]) if c not in xs)
            assert all(x % p**(4 - rows[j][0]) == 0 for j in range(n) for x in rows[j][1]), 'Hodge divisibility'
            tot += sum(rows[j][1][xin[j]] for j in range(n))
            # the slope-1 polynomial agrees with the N2 run
            idx3 = [j for j in range(n) if rows[j][0] == 3]
            B = nmod_mat(len(idx3), len(idx3), [(rows[j][1][xin[i]] // p) % p for i in idx3 for j in idx3], p)
            assert B.charpoly() == unit_poly(r, p, 'N2')[1]
        t = tot % p**3
        t = t if t < p**3 // 2 else t - p**3
        et = EIGENTRACE.get(p)
        print(f'  p = {p}: full 96-dimensional trace mod p^3 = {t}; point count {POINTCOUNT.get(p)}; '
              f'from the posted eigen-traces {None if et is None else 2*et[0] - et[1]}')

if __name__ == '__main__':
    main()


# ---------------------------------------------------------------------------------------------
# Powers of Frobenius.  A sub-object defined over a number field is only stable under a power
# Frob^f.  The factor degrees of the characteristic polynomial of Frob^f over Q_p are the same as
# for Frob unless sigma^k(alpha)/alpha is a root of unity for two distinct conjugate roots.  For a
# unit root alpha in the unramified extension of degree d write alpha = teich(alpha)(1 + p eps);
# then alpha^(p^d - 1) = 1 - p eps mod p^2, and sigma^k(alpha)/alpha is a root of unity only if
# eps mod p is fixed by sigma^k.  So it is enough that eps mod p generates F_{p^d}.
# Needs the unit-root polynomial mod p^2, i.e. all columns of Frob mod p^3 (the N3 runs).
from flint import nmod_poly, fmpz_poly

def unit_factors_mod_p2(r, p):
    d, rows, xin = load(r, p, 'N3'); n = len(xin)
    M = fmpz_mat(n, n, [(rows[j][1][xin[i]] // p) % p**2 for i in range(n) for j in range(n)])   # Frob/p mod p^2
    chi = [int(c) % p**2 for c in M.charpoly().coeffs()]
    chi_p = nmod_poly(chi, p)
    out = []
    for h, e in chi_p.factor()[1]:
        if h.degree() == 1 and int(h[0]) == 0: continue          # the factor T (slope > 0 part)
        if e != 1: return None                                   # not squarefree mod p
        c = chi_p // h                                           # coprime to h
        # one Hensel step: (h + p h1)(c + p c1) = chi mod p^2,  h1 = e c^(-1) mod h
        prod = fmpz_poly([int(x) for x in h.coeffs()]) * fmpz_poly([int(x) for x in c.coeffs()])
        diff = [(a - int(prod[i])) for i, a in enumerate(chi)]
        assert all(x % p == 0 for x in diff)
        ee = nmod_poly([(x // p) % p for x in diff], p)
        g, s, t = h.xgcd(c)                                      # s h + t c = 1
        assert g.degree() == 0
        h1 = (ee * t * nmod_poly([pow(int(g[0]), -1, p)], p)) % h
        hh = [int(h[i]) + p * int(h1[i]) for i in range(h.degree() + 1)]
        out.append((h, nmod_poly(hh, p**2)))
    return out

def power_stable(r, p):
    """True if no ratio of two distinct Q_p-conjugate unit roots can be a root of unity."""
    res = []
    fs = unit_factors_mod_p2(r, p)
    if fs is None: return None
    for h, hh in fs:
        d = h.degree()
        if d == 1: res.append((1, True)); continue
        x = nmod_poly([0, 1], p**2); acc = nmod_poly([1], p**2); e = p**d - 1
        base = x % hh
        while e:
            if e & 1: acc = (acc * base) % hh
            base = (base * base) % hh; e >>= 1
        co = [int(acc[i]) - (1 if i == 0 else 0) for i in range(d)]
        assert all(c % p == 0 for c in co)
        w = nmod_poly([(c // p) % p for c in co], p)             # = -eps mod p, in F_p[T]/(h)
        ok = True
        for l in {q for q in range(2, d + 1) if d % q == 0 and all(q % t for t in range(2, q))}:
            k = d // l
            wp = w
            for _ in range(k):
                wp = pow_mod(wp, p, h)
            ok &= (wp != w)
        res.append((d, ok))
    return res

def pow_mod(a, e, h):
    acc = nmod_poly([1], h.modulus()); base = a % h
    while e:
        if e & 1: acc = (acc * base) % h
        base = (base * base) % h; e >>= 1
    return acc

def powers():
    primes = sorted({int(f.split('_p')[1].split('_')[0]) for f in os.listdir(D) if f.endswith('_N3.txt')})
    print('Powers of Frobenius (unit-root polynomials mod p^2): factor degree, "no root-of-unity ratio" certified')
    for p in primes:
        for r, name in ((1, 'slope 1'), (2, 'slope 2')):
            ps = power_stable(r, p)
            print(f'  p = {p:3d} {name}:', 'not squarefree mod p' if ps is None else ' '.join(f'{d}:{"yes" if ok else "NO"}' for d, ok in sorted(ps)))

if __name__ == '__main__':
    powers()
````

</details>

<details>
<summary><code>validate/validate.py</code>: comparison with the unpatched program on two curves</summary>

````python
"""Validation of the coset patch against the unpatched program on two curves.
  g2 : y^2 = x^6 + 3x^4 + 5x^2 + 7 over F_13, involution x -> -x        (pieces: x-exponent even / odd)
  pic: y^3 = x^4 + 2x^3 + 5x + 3 over F_13, automorphism y -> zeta_3 y  (pieces: y-exponent 1, 2 mod 3;
       Hodge numbers (2,1) and (1,2), not symmetric)
The product of the characteristic polynomials of the pieces must equal the zeta polynomial computed by the
stock readfile.exe.   usage: python3 validate.py <dir of the patched ToricControlledReduction build>"""
import sys, os, subprocess, tempfile
from flint import fmpz_mat, fmpz_poly
B = os.path.join(sys.argv[1], 'build', 'examples'); here = os.path.dirname(os.path.abspath(__file__))
def piece(inp, cons, N, tmp):
    out = os.path.join(tmp, 'o.txt')
    subprocess.run([os.path.join(B, 'coset_frob.exe'), inp, out, cons, N], check=True, stdout=subprocess.DEVNULL)
    d = {}; rows = {}
    for line in open(out):
        if line.startswith('row'):
            h, v = line.split(':'); rows[int(h.split()[1])] = [int(x) for x in v.split()]
        else:
            k, _, v = line.strip().partition(' '); d[k] = v.strip()
    xin = [int(x) for x in d['X_in_Y'].split()]; n = len(xin)
    if n == 0: return fmpz_poly([1])
    return fmpz_mat(n, n, [rows[j][xin[i]] for i in range(n) for j in range(n)]).charpoly()
ok = True
with tempfile.TemporaryDirectory() as tmp:
    for name, cons, N, mod in (('g2', ['1 0 2 0', '1 0 2 1'], '4,3', 13**3), ('pic', ['0 1 3 0', '0 1 3 1', '0 1 3 2'], '5,4', 13**4)):
        inp = os.path.join(here, f'in_{name}.txt'); ref = os.path.join(tmp, 'ref.txt')
        subprocess.run([os.path.join(B, 'readfile.exe'), inp, ref], check=True, stdout=subprocess.DEVNULL)
        zeta = [int(x) for x in open(ref).read().strip().split(':')[-1].strip('[]').split(',')]
        prod = fmpz_poly([1])
        for c in cons: prod *= piece(inp, c, N, tmp)
        got = [int(c) % mod for c in prod.coeffs()]
        same = got == [z % mod for z in zeta]
        ok &= same
        print(name, 'stock zeta', zeta, '| product of pieces mod', mod, 'agrees:', same)
print('ALL OK' if ok else 'FAILED')
````

</details>

<details>
<summary><code>validate/in_g2.txt</code>: input for the genus-2 curve</summary>

````text
g2:[[0,2],[6,0],[4,0],[2,0],[0,0]]:[1,-1,-3,-5,-7]:[[1,0],[0,1],[-1,-3]]:[0,0,6]:13
````

</details>

<details>
<summary><code>validate/in_pic.txt</code>: input for the Picard curve</summary>

````text
pic:[[0,3],[4,0],[3,0],[1,0],[0,0]]:[1,-1,-2,-5,-3]:[[1,0],[0,1],[-3,-4]]:[0,0,12]:13
````

</details>

<details>
<summary><code>pointcount.py</code>: independent traces by point counting</summary>

````python
"""Independent checks from point counts at p:
   #T(F_p) = 1 + p + p^2 + p^3 - Tr(Frob | H^3(T)),  T: u^3 + H = 0 in P(1,1,1,1,2);
   the quadratic twist in (c,d) gives Tr(sigma Frob), hence the traces on the sigma-even and sigma-odd parts."""
import sys, numpy as np
p = int(sys.argv[1]); k = 5*pow(7, -1, p) % p
eps = next(e for e in range(2, p) if pow(e, (p-1)//2, p) == p-1)      # a non-residue
r = np.arange(p, dtype=np.int64)
a, b, c, d = np.meshgrid(r, r, r, r, indexing='ij')
tab = lambda n: np.array([pow(int(t), n, p) for t in range(p)], dtype=np.int64)
P5, P6 = tab(5), tab(6)
def trace(e):          # e = 1: T itself; e = eps: twist (c,d) -> sqrt(eps) (c,d)
    e2, e3 = e*e % p, pow(e, 3, p)
    H = (P6[a] + P6[b] + k*P5[a]*b + 2*k*a*P5[b] + e3*(P6[c] + P6[d] + k*P5[c]*d + 3*k*c*P5[d])
         + k*a*b*c*d % p*(e*a*a + 2*e2*c*c)) % p
    cubes = np.zeros(p, dtype=np.int64)
    for u in range(p): cubes[(-pow(u, 3, p)) % p] += 1
    N_aff = int(cubes[H].sum()); assert (N_aff - 1) % (p - 1) == 0
    return 1 + p + p*p + p**3 - (N_aff - 1)//(p - 1)
t1, t2 = trace(1), trace(eps)
print(f'p={p}: Tr(Frob | H^3) = {t1}, twisted = {t2}; sigma-even part {(t1+t2)//2}, sigma-odd part {(t1-t2)//2}')
````

</details>

<details>
<summary><code>lattice_check.py</code>: the invariant ring and the cosets are generated in degree 1</summary>

````python
"""Combinatorial preconditions for the coset-restricted controlled reduction on T: u^3 + H = 0.
Points are (b,c,d,u) >= 0 with b+c+d+2u <= 6k (level k).  M' = {c+d even, u = 0 mod 3};
coset (par, r) = {c+d = par mod 2, u = r mod 3}."""
import itertools
def level_points(k, par, r):
    out = set()
    for u in range(r, 3*k + 1, 3):
        m = 6*k - 2*u
        for c in range(m + 1):
            for d in range(m - c + 1):
                if (c + d) % 2 != par: continue
                for b in range(m - c - d + 1): out.add((b, c, d, u))
    return out
ring = {k: level_points(k, 0, 0) for k in range(0, 8)}
R1 = sorted(ring[1])
print('ring points per level:', [len(ring[k]) for k in range(6)])
# ring generated in degree 1 (needed for peeling monomials of f^j): every point of level k >= 1 is (level k-1) + (level 1)
ok = all(any(tuple(x - y for x, y in zip(w, v)) in ring[k-1] for v in R1) for k in range(1, 8) for w in ring[k])
print('ring: every level-k point is a level-(k-1) point plus a level-1 ring point (k <= 7):', ok)
for par, r in ((1, 1), (1, 2), (0, 1), (0, 2), (1, 0)):
    mod = {k: level_points(k, par, r) for k in range(0, 8)}
    gen = all(any(tuple(x - y for x, y in zip(w, v)) in mod[k-1] for v in R1) for k in range(2, 8) for w in mod[k])
    # interior points (strict inequalities, all coordinates >= 1 and b+c+d+2u < 6k)
    inter = [sum(1 for (b, c, d, u) in mod[k] if min(b, c, d, u) >= 1 and b + c + d + 2*u < 6*k) for k in range(1, 5)]
    print(f'coset (c+d={par} mod 2, u={r} mod 3): points per level {[len(mod[k]) for k in range(6)]}, '
          f'generated over the ring from level 1 (k <= 7): {gen}, interior points levels 1..4: {inter}')
````

</details>

---
_Generated by [Claude Code](https://claude.ai/code)_
