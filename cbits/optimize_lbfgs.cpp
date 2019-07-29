#include <Eigen/Core>
#include <iostream>
#include <LBFGS.h>

using Eigen::VectorXd;
using namespace LBFGSpp;

// A function that can be optimized
typedef double (*optfun) (const VectorXd& x, VectorXd& grad);

// C++ wrapper around a C function pointer, for use with LBFGS++
class WrappedFun {
private:
  optfun f;
public:
  WrappedFun (optfun f_in) { f = f_in; }
  double operator()(const VectorXd& x, VectorXd& grad) {
    return f (x, grad);
  }
};

// External entrypoint to call LBFGS++
extern "C" double optimize_lbfgs (optfun f, VectorXd& params) {
  // Set up parameters
  LBFGSParam<double> param;
  param.epsilon = 1e-6;
  param.max_iterations = 100;

  // Create solver and function objects, and return value slot
  LBFGSSolver<double> solver(param);
  WrappedFun fun (f);
  double val;

  // Call solver
  solver.minimize (fun, params, val);
  return val;
}
