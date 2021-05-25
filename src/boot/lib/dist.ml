



let gaussianSample mu sigma =
  Owl_stats.gaussian_rvs ~mu:mu ~sigma:sigma

let gaussianPDF x mu sigma =
  Owl_stats.gaussian_pdf x ~mu:mu ~sigma:sigma

let gaussianLogPDF x mu sigma =
  Owl_stats.gaussian_logpdf x ~mu:mu ~sigma:sigma


let bernoulliSample p =
  Owl_stats.binomial_rvs ~p:p ~n:1

let bernoulliPDF x p =
  Owl_stats.binomial_pdf x ~p:p ~n:1

let bernoulliLogPDF x p =
  Owl_stats.binomial_logpdf x ~p:p ~n:1
