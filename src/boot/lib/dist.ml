



let gaussianSample mu sigma =
  Owl_stats.gaussian_rvs ~mu:mu ~sigma:sigma

let gaussianPDF x mu sigma =
  Owl_stats.gaussian_pdf x ~mu:mu ~sigma:sigma

let gaussianLogPDF x mu sigma =
  Owl_stats.gaussian_logpdf x ~mu:mu ~sigma:sigma
