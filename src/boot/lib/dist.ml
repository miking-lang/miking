



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



let binomialSample p n =
  Owl_stats.binomial_rvs ~p:p ~n:n

let binomialPDF x p n =
  Owl_stats.binomial_pdf x ~p:p ~n:n

let binomialLogPDF x p n =
  Owl_stats.binomial_logpdf x ~p:p ~n:n



let betaSample a b =
  Owl_stats.beta_rvs ~a:a ~b:b

let betaPDF x a b =
  Owl_stats.beta_pdf x ~a:a ~b:b

let betaLogPDF x a b =
  Owl_stats.beta_logpdf x ~a:a ~b:b



let exponentialSample lambda =
  Owl_stats.exponential_rvs ~lambda:lambda

let exponentialPDF x lambda =
  Owl_stats.exponential_pdf x ~lambda:lambda

let exponentialLogPDF x lambda =
  Owl_stats.exponential_logpdf x ~lambda:lambda
