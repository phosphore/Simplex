using System;

namespace Simplex
{

    class Program
    {
        public const int INFEASIBLE = 0;
        public const int OPTIMAL = 1;
        public const int UNBOUNDED = 2;
        public const float MAXITERATIONS = float.PositiveInfinity;

        static void Main(string[] args)
        {
            float[] x;
            int status = -1; // status flag
            float[][] A = new float[][] { new float[] { 4f, 3f }, new float[] { 2f, 4f } }; // A matrix containing the constraints coefficients.
            float[] b = new float[2] { 240f, 160f }; // A column array containing the right-hand side value for each constraint in the constraint matrix.
            float[] c = new float[2] { 15f, 21f }; // A column array containing the objective function coefficients.
            int m = 2; // the number of equations (= A.Length;)
            int n = 2; // the number of variables (= A[0].Length;)
            float[] xLB = new float[2] { 0f, 0f }; // An array containing the lower bound on each of the variables.
            float[] xUB = new float[2] { float.PositiveInfinity, float.PositiveInfinity }; // An array containing the upper bound on each of the variables.
            
            int i, j, k;
            float[] varStatus = new float[n + m];
            int[] basicVars = new int[m];
            float[][] Binv = new float[m][];
            for (i = 0; i < m; i++) { Binv[i] = new float[m]; }
            float[] cBT = new float[m];
            float[] pi = new float[m];
            float[] rc = new float[n];
            float[] BinvAs = new float[m];

            // Some useful constants
            float BASIC = 0f, NONBASIC_L = +1f, NONBASIC_U = -1f;
            float TOL = 0.000001f;

            // The solution
            x = new float[n + m];




            // Create the initial solution to Phase 1
            // - Real variables
            for (i = 0; i < n; i++)
            {
                var absLB = Math.Abs(xLB[i]);
                var absUB = Math.Abs(xUB[i]);
                x[i] = (absLB < absUB) ? xLB[i] : xUB[i];
                varStatus[i] = (absLB < absUB) ? NONBASIC_L : NONBASIC_U;
            }
            // - Artificial variables
            for (i = 0; i < m; i++)
            {
                x[i + n] = b[i];
                // Some of the real variables might be non-zero, so need
                // to reduce x[artificials] accordingly
                for (j = 0; j < n; j++) { x[i + n] -= A[i][j] * x[j]; }
                varStatus[i + n] = BASIC;
                basicVars[i] = i + n;
            }
            // - Basis
            for (i = 0; i < m; i++) { cBT[i] = +1.0f; }
            for (i = 0; i < m; i++)
            {
                for (j = 0; j < m; j++)
                {
                    Binv[i][j] = (i == j) ? 1.0f : 0.0f;
                }
            }

            // Being simplex iterations
            bool phaseOne = true;
            int iter = 0;
            var z = 0.0f;
            while (true)
            {
                iter++;
                if (iter >= MAXITERATIONS)
                {
                    z = 0.0f;
                    for (i = 0; i < n; i++) z += c[i] * x[i];
                    break;
                }

                //---------------------------------------------------------------------
                // Step 1. Duals and reduced Costs
               
                for (i = 0; i < m; i++)
                {
                    pi[i] = 0.0f;
                    for (j = 0; j < m; j++)
                    {
                        pi[i] += cBT[j] * Binv[j][i];
                    }
                }
                for (j = 0; j < n; j++)
                {
                    rc[j] = phaseOne ? 0.0f : c[j];
                    for (i = 0; i < m; i++)
                    {
                        rc[j] -= pi[i] * A[i][j];
                    }
                }
               
                //---------------------------------------------------------------------

                //---------------------------------------------------------------------
                // Step 2. Check optimality and pick entering variable
                var minRC = -TOL;
                int s = -1;
                for (i = 0; i < n; i++)
                {
                    // If NONBASIC_L (= +1), rc[i] must be negative (< 0) -> +rc[i] < -TOL
                    // If NONBASIC_U (= -1), rc[i] must be positive (> 0) -> -rc[i] < -TOL
                    //                                                      -> +rc[i] > +TOL
                    // If BASIC    (= 0), can't use this rc -> 0 * rc[i] < -LPG_TOL -> alway FALSE
                    // Then, by setting initial value of minRC to -TOL, can collapse this
                    // check and the check for a better RC into 1 IF statement!
                    if (varStatus[i] * rc[i] < minRC)
                    {
                        minRC = varStatus[i] * rc[i];
                        s = i;
                    }
                }
                
                // If no entering variable
                if (s == -1)
                {
                    if (phaseOne)
                    {
                      
                        z = 0.0f;
                        for (i = 0; i < m; i++) z += cBT[i] * x[basicVars[i]];
                        if (z > TOL)
                        {
                           
                            status = INFEASIBLE;
                            break;
                        }
                        else
                        {
                            phaseOne = false;
                            for (i = 0; i < m; i++)
                            {
                                cBT[i] = (basicVars[i] < n) ? (c[basicVars[i]]) : (0.0f);
                            }
                            continue;
                        }
                    }
                    else
                    {
                        status = OPTIMAL;
                        z = 0.0f;
                        for (i = 0; i < n; i++)
                        {
                            z += c[i] * x[i];
                        }
                        
                        break;
                    }
                }
                //---------------------------------------------------------------------

                //---------------------------------------------------------------------
                // Step 3. Calculate BinvAs
                for (i = 0; i < m; i++)
                {
                    BinvAs[i] = 0.0f;
                    for (k = 0; k < m; k++) BinvAs[i] += Binv[i][k] * A[k][s];
                }
              
                //---------------------------------------------------------------------

                //---------------------------------------------------------------------
                // Step 4. Ratio test
                float minRatio = float.PositiveInfinity, ratio = 0.0f;
                int r = -1;
                var rIsEV = false;
                // If EV is...
                // NBL, -> rc[s] < 0 -> want to INCREASE x[s]
                // NBU, -> rc[s] > 0 -> want to DECREASE x[s]
                // Option 1: Degenerate iteration
                ratio = xUB[s] - xLB[s];
                if (ratio <= minRatio) { minRatio = ratio; r = -1; rIsEV = true; }
                // Option 2: Basic variables leaving basis
                for (i = 0; i < m; i++)
                {
                    j = basicVars[i];
                    var jLB = (j >= n) ? 0.0f : xLB[j];
                    var jUB = (j >= n) ? float.PositiveInfinity : xUB[j];
                    if (-1 * varStatus[s] * BinvAs[i] > +TOL)
                    { // NBL: BinvAs[i] < 0, NBU: BinvAs[i] > 0
                        ratio = (x[j] - jUB) / (varStatus[s] * BinvAs[i]);
                        if (ratio <= minRatio) { minRatio = ratio; r = i; rIsEV = false; }
                    }
                    if (+1 * varStatus[s] * BinvAs[i] > +TOL)
                    { // NBL: BinvAs[i] > 0, NBU: BinvAs[i] < 0
                        ratio = (x[j] - jLB) / (varStatus[s] * BinvAs[i]);
                        if (ratio <= minRatio) { minRatio = ratio; r = i; rIsEV = false; }
                    }
                }

                // Check ratio
                if (minRatio >= float.PositiveInfinity)
                {
                    if (phaseOne)
                    {
                        // nothing good!

                        break;
                    }
                    else
                    {
                        // PHASE 2: Unbounded!
                        status = UNBOUNDED;
                      
                        break;
                    }
                }
                //---------------------------------------------------------------------

                //---------------------------------------------------------------------
                // Step 5. Update solution and basis
                x[s] += varStatus[s] * minRatio;
                for (i = 0; i < m; i++) x[basicVars[i]] -= varStatus[s] * minRatio * BinvAs[i];

                if (!rIsEV)
                {
                    // Basis change! Update Binv, flags
                    // RSM tableau: [Binv B | Binv | Binv As]
                    // -> GJ pivot on the BinvAs column, rth row
                    var erBinvAs = BinvAs[r];
                    // All non-r rows
                    for (i = 0; i < m; i++)
                    {
                        if (i != r)
                        {
                            var eiBinvAsOvererBinvAs = BinvAs[i] / erBinvAs;
                            for (j = 0; j < m; j++)
                            {
                                Binv[i][j] -= eiBinvAsOvererBinvAs * Binv[r][j];
                            }
                        }
                    }
                    // rth row
                    for (j = 0; j < m; j++) Binv[r][j] /= erBinvAs;

                    // Update status flags
                    varStatus[s] = BASIC;
                    if (basicVars[r] < n)
                    {
                        if (Math.Abs(x[basicVars[r]] - xLB[basicVars[r]]) < TOL) varStatus[basicVars[r]] = NONBASIC_L;
                        if (Math.Abs(x[basicVars[r]] - xUB[basicVars[r]]) < TOL) varStatus[basicVars[r]] = NONBASIC_U;
                    }
                    else
                    {
                        if (Math.Abs(x[basicVars[r]] - 0.00000) < TOL) varStatus[basicVars[r]] = NONBASIC_L;
                        if (Math.Abs(x[basicVars[r]] - float.PositiveInfinity) < TOL) varStatus[basicVars[r]] = NONBASIC_U;
                    }
                    cBT[r] = phaseOne ? 0.0f : c[s];
                    basicVars[r] = s;

                }
                else
                {
                    // Degenerate iteration
                    if (varStatus[s] == NONBASIC_L) { varStatus[s] = NONBASIC_U; }
                    else { varStatus[s] = NONBASIC_L; }
                }
                //---------------------------------------------------------------------
            }


            Console.WriteLine("Z     : " + z);
            Console.WriteLine("status: " + status + '\n');
            Console.WriteLine("X:");
            foreach (var res in x)
                Console.WriteLine(res.ToString());
            Console.ReadKey();
            
        }
    }
}          



