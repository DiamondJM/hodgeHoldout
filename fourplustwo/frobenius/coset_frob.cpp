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
