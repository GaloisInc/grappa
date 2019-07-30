#include <Eigen/Core>
#include <iostream>
#include <LBFGS.h>

using Eigen::VectorXd;
using namespace LBFGSpp;

typedef struct VectorRep {
  double *vdata;
  Eigen::Index vsize;
} VectorRep;

// A function that can be optimized
typedef double (*optfun) (const double *x, double *grad);

// C++ wrapper around a C function pointer, for use with LBFGS++
class WrappedFun {
private:
  optfun f;
public:
  WrappedFun (optfun f_in) { f = f_in; }
  double operator()(const VectorXd& x, VectorXd& grad) {
    return f (((VectorRep*)&x)->vdata, ((VectorRep*)&grad)->vdata);
  }
};

// External entrypoint to call LBFGS++
extern "C" double optimize_lbfgs (optfun f, uint32_t size, double *init_xs) {
  // Set up parameters
  LBFGSParam<double> param;
  param.epsilon = 1e-6;
  param.max_iterations = 100;

  // Create solver and function objects, and return value slot
  VectorRep init_rep = { init_xs, size };
  VectorXd *vect = (VectorXd*)&init_rep;
  LBFGSSolver<double> solver(param);
  WrappedFun fun (f);
  double val;

  // Call solver
  solver.minimize (fun, *vect, val);
  return val;
}
