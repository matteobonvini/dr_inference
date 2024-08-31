library("drtmle")
library("SuperLearner")

set.seed(082024)

r.estimator <- function(y, a, ahat, bhat, kern) {
  # Estimate the second-order remainder R_n
  n <- length(a)
  
  # generate indices for computing U-statistic
  u.idx <- expand.grid(1:n, 1:n)
  u.idx <- u.idx[u.idx[, 1] != u.idx[, 2], ]
  u.idx1 <- u.idx[, 1]
  u.idx2 <- u.idx[, 2]
  
  # select bandwidth as the one that we would choose to regress
  # (Y - bhat) on (A = 1, ahat, bhat). Other approaches possible.
  h <- sm::h.select(x=cbind(ahat[a==1], bhat[a==1]),
                    y=(y-bhat)[a==1], method="cv")
  h.a <- max(h[1], max(diff(sort(ahat), lag=2)))
  h.b <- max(h[2], max(diff(sort(bhat), lag=2)))
  K2 <- function(x, x0, h) kern((x-x0)/h)/h
  K.a <- K2(ahat[u.idx1], ahat[u.idx2], h=h.a)
  K.b <- K2(bhat[u.idx1], bhat[u.idx2], h=h.b)
  K.ab <- K.a*K.b
  
  idx.a <- K.a > 0 
  u.idx2a <- u.idx2[idx.a]
  u.idx1a <- u.idx1[idx.a]
  K.a2 <- K.a[idx.a]
  
  idx.b <- K.b > 0
  u.idx2b <- u.idx2[idx.b]
  u.idx1b <- u.idx1[idx.b]
  K.b2 <- K.b[idx.b]
  
  idx.ab <- K.ab > 0
  u.idx2ab <- u.idx2[idx.ab]
  u.idx1ab <- u.idx1[idx.ab]
  K.ab2 <- K.ab[idx.ab]
  
  Qhat.a <- tapply(a[u.idx1] * K.a, u.idx2, sum) / (n-1)
  Qhat.b <- tapply(a[u.idx1] * K.b, u.idx2, sum) / (n-1)
  Qhat.ab <- tapply(a[u.idx1] * K.ab, u.idx2, sum) / (n-1)
  
  proj.K.a <- K.a2 / Qhat.a[u.idx2a]
  proj.K.b <- K.b2 / Qhat.b[u.idx2b]
  proj.K.ab <- K.ab2 / Qhat.ab[u.idx2ab]
  proj.K.ab[(a[u.idx1ab]==0) | (K.ab2==0)] <- 0
  proj.K.a[a[u.idx1a]==0] <- 0
  proj.K.b[a[u.idx2b]==0] <- 0
  
  summ.a <- (a[u.idx2a] / ahat[u.idx2a] - 1) *
    proj.K.a * (a[u.idx1a] * (y[u.idx1a] - bhat[u.idx1a]))
  summ.b <-  (a[u.idx2b] * (y[u.idx2b] - bhat[u.idx2b])) *
    proj.K.b * (a[u.idx1b] / ahat[u.idx1b] - 1)
  summ.ab <- (a[u.idx2ab] / ahat[u.idx2ab] - 1) *
    proj.K.ab * (a[u.idx1ab] * (y[u.idx1ab] - bhat[u.idx1ab]))
  
  if.vals.a <- rep(0, n)
  if.vals.a[which(tapply(idx.ab, u.idx2, mean) > 0)] <-
    tapply(summ.ab, u.idx2ab, sum) / (n-1)
  
  if.vals.b <- rep(0, n)
  if.vals.b[which(tapply(idx.ab, u.idx1, mean) > 0)] <-
    tapply(summ.ab, u.idx1ab, sum) / (n-1)
  # check if there are some "holes," that is the bw is too small and there
  # are no observations within window.
  tot.na.a <- sum(is.na(summ.a))
  tot.na.b <- sum(is.na(summ.b))
  tot.na.ab <- sum(is.na(summ.ab))
  if(tot.na.a > 0) {
    print(paste0("A total of ", tot.na.a, " NAs removed for est.a"))
  }
  if(tot.na.b > 0) {
    print(paste0("A total of ", tot.na.b, " NAs removed for est.b"))
  }
  if(tot.na.ab > 0) {
    print(paste0("A total of ", tot.na.ab, " NAs removed for est.ab"))
  }
  
  # compute the U-statistics, ignoring cases where there are no observations.
  est.a <- sum(summ.a, na.rm=TRUE) / (n*(n-1)-tot.na.a)
  est.b <- sum(summ.b, na.rm=TRUE) / (n*(n-1)-tot.na.b)
  est.ab <- sum(summ.ab, na.rm=TRUE) / (n*(n-1)-tot.na.ab)
  
  est <- list(est.a = est.a, est.b=est.b, est.ab=est.ab, if.vals.a=if.vals.a,
              if.vals.b=if.vals.b)
  return(est)
}

estimator <- function(y, a, ahat, bhat, kern, h, guard) {
  
  # Compute AIPW estimator (est.dr)
  n <- length(a)
  if.vals <- a/ahat*(y-bhat) + bhat
  est.dr <- mean(if.vals)
  se <- sqrt(mean((if.vals-est.dr)^2)/n)
  
  if(guard == "FALSE") {
    est.a <- est.b <- est.ab <- se.corr <- NULL
  } else {
    bias.corr <- r.estimator(y=y, a=a, ahat=ahat, bhat=bhat, kern=kern)
    est.a <- est.dr - bias.corr$est.a
    est.b <- est.dr - bias.corr$est.b
    est.ab <- est.dr - bias.corr$est.ab
    se.corr <- sqrt(var(if.vals-bias.corr$if.vals.a-bias.corr$if.vals.b)/n)
  }
  
  return(list(est.dr=est.dr, 
              est.a=est.a,
              est.b=est.b,
              est.ab=est.ab,
              se=se,
              se.corr=se.corr))
}

##### Simulation begins #####
# Notation:
# a.x = P(A = 1 | X = x)
# ahat = \hat{P}(A = 1 | X)
# b.x = P(Y = 1 | X = x)
# bhat = \hat{P}(Y = 1 X)

expit <- function(x) 1/(1+exp(-x))
kern <- function(x) 0.5*I(abs(x)<=1)
a.x <- function(beta, x1, x2) expit(beta[1] + beta[2]*x1 + beta[3]*x2)
b.x <- function(beta, x1, x2) expit(beta[1] + beta[2]*x1 + beta[3]*x2)
beta.a <- c(-1, 2, 0.5)
beta.b <- c(-2.5, 5, 2)
truth <- pracma::quad2d(b.x, beta=beta.b, 0, 1, 0, 1)
nsim <- 500
sample.sizes <- c(500, 1000, 1500, 2000)
error.rates.a <- c(0, 0.3) # n^(-error.rates.a)
error.rates.b <- c(0, 0.3) # n^(-error.rates.b)

res <- data.frame(n = numeric(),
                  a.err = numeric(),
                  b.err = numeric(),
                  oracle.est = numeric(),
                  oracle.se = numeric(),
                  aipw.est = numeric(),
                  aipw.se = numeric(),
                  corrA.est = numeric(),
                  corrB.est = numeric(),
                  corr.est = numeric(),
                  tmle.est = numeric(),
                  tmle.se=numeric())

SL.lib.drtmle <- c("SL.mean", "SL.speedlm", "SL.speedglm",
                   "SL.glm.interaction", "SL.glm", "SL.gam", "SL.rpart")
system.time({
  for(n in sample.sizes){
    for(err.a in error.rates.a) {
      for(err.b in error.rates.b) {
        for(j in 1:nsim) {
          # generate data
          x1 <- runif(n)
          x2 <- runif(n)
          # oracle nuisances
          ahat.or <- a.x(beta.a, x1, x2)
          bhat.or <- b.x(beta.b, x1, x2)
          
          x <- data.frame(x1=x1, x2=x2)
          a <- rbinom(n, size=1, ahat.or)
          y1 <- rbinom(n, size=1, bhat.or)
          y0 <- rbinom(n, size=1, 0.5)
          y <- a*y1 + (1-a)*y0
          
          betah.a <- beta.a + rnorm(3, mean = n^(-err.a), sd = n^(-err.a))
          betah.b <- beta.b + rnorm(3, mean = n^(-err.b), sd = n^(-err.b))
          
          bhat <- b.x(betah.b, x1, x2)
          ahat <- a.x(betah.a, x1, x2)
          
          # place them in the right format for drtmle
          Qn <- list(bhat)
          gn <- list(ahat)
          tmle.est <- drtmle(Y=y, A=a, W=x, a_0=1, Qn=Qn, gn=gn, 
                             SL_Qr=SL.lib.drtmle, SL_gr=SL.lib.drtmle)
          drtmle.se <- sqrt(tmle.est$drtmle$cov)
          aipw <- estimator(y, a, ahat, bhat, kern, guard="TRUE")
          if(j %% 50 == 0) print(c(j, round(aipw$se.corr, 5), 
                                   round(drtmle.se, 5), n, err.a, err.b))
          oracle <- estimator(y, a, ahat.or, bhat.or, kern, guard="FALSE")
          
          new.res <- data.frame(n=n,
                                a.err=err.a,
                                b.err=err.b,
                                oracle.est=oracle$est.dr,
                                oracle.se=oracle$se,
                                aipw.est=aipw$est.dr,
                                aipw.se=aipw$se,
                                corrA.est=aipw$est.a,
                                corrB.est=aipw$est.b,
                                corr.est=aipw$est.ab,
                                corr.se=aipw$se.corr,
                                tmle.est=tmle.est$drtmle$est,
                                tmle.se=drtmle.se)
          res <- rbind(res, new.res)
        }
      }
    }
  }
})