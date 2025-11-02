devtools::install_github("vdorie/aciccomp/2017")
library(aciccomp2017)
W <- aciccomp2017::input_2017
corr <- aipw <- se <- se.corr <- err.corr <- err.aipw <- cov.corr <- cov.aipw <- rep(NA, 250)
setting <- 24
for(i in 1:250) {
  data <- dgp_2017(setting, i)
  A <- data$z
  Y <- data$y
  ATE <- mean(data$alpha)
  dat.pi <- cbind(A=as.factor(A), W)
  dat <- cbind(Y=Y, A=A, W)
  preds.pi <- predict(glm(A ~ ., data=dat.pi, family=binomial()), 
                      type = "response")
  mu.x <- lm(Y ~ ., data=dat)
  preds1 <- predict(mu.x, newdata=cbind(A=1, W))
  preds0 <- predict(mu.x, newdata=cbind(A=0, W))
  
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
  
  estimator <- function(y, a, ahat, bhat, kern, guard) {
    
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
                se.corr=se.corr, 
                if.vals=if.vals, 
                if.vals.corr=if.vals-bias.corr$if.vals.a-bias.corr$if.vals.b))
  }
  kern <- function(x) 0.5 * I(abs(x) <= 1)
  n <- length(Y)
  t1 <- estimator(y=Y, a=A, ahat=preds.pi, bhat=preds1, kern=kern, 
                  guard="TRUE")
  t0 <- estimator(y=Y, a=1-A, ahat=1-preds.pi, bhat=preds0, kern=kern, 
                  guard="TRUE")
  corr[i] <- t1$est.ab - t0$est.ab
  se.corr[i] <- sqrt(var(t1$if.vals.corr - t0$if.vals.corr)/n)
  if.vals <- A/preds.pi*(Y-preds1) + preds1 - (1-A)/(1-preds.pi)*(Y-preds0) - preds0
  aipw[i] <- mean(if.vals)
  se[i] <- sqrt(var(if.vals)/n)
  err.corr[i] <- corr[i] - ATE
  err.aipw[i] <- aipw[i] - ATE
  cov.corr[i] <- abs(err.corr[i]) <= 1.96*se.corr[i]
  cov.aipw[i] <- abs(err.aipw[i]) <= 1.96*se[i]
  print(mean(abs(err.corr), na.rm=TRUE))
  print(mean(abs(err.aipw), na.rm=TRUE))
  print(mean(abs(cov.corr), na.rm=TRUE))
  print(mean(abs(cov.aipw), na.rm=TRUE))
  print(i)
}