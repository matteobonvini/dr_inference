setwd(dirname(rstudioapi::getActiveDocumentContext()$path))
library(drtmle)
library(SuperLearner)
library(ggplot2)

set.seed(022024)

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
  h <- sm::h.select(x = cbind(ahat[a == 1], bhat[a == 1]),
                    y = (y - bhat)[a == 1], method = "cv")
  h.a <- max(h[1], max(diff(sort(ahat), lag = 2)))
  h.b <- max(h[2], max(diff(sort(bhat), lag = 2)))
  # h.a <- h.b <- n^(-0.25)
  
  K2 <- function(x, x0, h) kern((x - x0) / h) / h
  K.a <- K2(ahat[u.idx1], ahat[u.idx2], h = h.a)
  K.b <- K2(bhat[u.idx1], bhat[u.idx2], h = h.b)
  K.ab <- K.a * K.b
  
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
  
  summ.a <- (a[u.idx2a] / ahat[u.idx2a] - 1) *
    proj.K.a * (a[u.idx1a] * (y[u.idx1a] - bhat[u.idx1a]))
  summ.b <-  (a[u.idx2b] * (y[u.idx2b] - bhat[u.idx2b])) *
    proj.K.b * (a[u.idx1b] / ahat[u.idx1b] - 1)
  summ.ab <- (a[u.idx2ab] / ahat[u.idx2ab] - 1) *
    proj.K.ab * (a[u.idx1ab] * (y[u.idx1ab] - bhat[u.idx1ab]))
  
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
  
  est <- list(est.a = est.a, est.b=est.b, est.ab=est.ab)
  return(est)
}

estimator <- function(y, a, ahat, bhat, kern, h, guard) {
  
  # Compute AIPW estimator (est.dr)
  n <- length(a)
  if.vals <- a/ahat*(y-bhat) + bhat
  est.dr <- mean(if.vals)
  se <- sqrt(mean((if.vals-est.dr)^2)/n)
  
  if(guard == "FALSE") {
    est.a <- est.b <- est.ab <- NULL
  } else {
    bias.corr <- r.estimator(y=y, a=a, ahat=ahat, bhat=bhat, kern=kern)
    est.a <- est.dr - bias.corr$est.a
    est.b <- est.dr - bias.corr$est.b
    est.ab <- est.dr - bias.corr$est.ab
  }

  return(list(est.dr=est.dr, 
              est.a=est.a,
              est.b=est.b,
              est.ab=est.ab,
              se=se))
}

##### Simulation begins #####
# Notation:
# a.x = P(A = 1 | X = x)
# ahat = \hat{P}(A = 1 | X)
# b.x = P(Y = 1 | A = 1, X = x)
# bhat = \hat{P}(Y = 1 | A = 1, X)

expit <- function(x) 1/(1+exp(-x))
kern <- function(x) 0.5*I(abs(x)<=1)
a.x <- function(beta, x1, x2) expit(beta[1] + beta[2]*x1 + beta[3]*x2)
b.x <- function(beta, x1, x2) expit(beta[1] + beta[2]*x1 + beta[3]*x2)
beta.a <- c(-1, 2, 0.5)
beta.b <- c(-2.5, 5, 2)
truth <- pracma::quad2d(b.x, beta=beta.b, 0, 1, 0, 1)
nsim <- 2
sample.sizes <- c(500, 1000, 2000, 4000)
error.rates.a <- c(-1, 0, 0.3) # n^(-error.rates.a)
error.rates.b <- c(-1, 0, 0.3) # n^(-error.rates.b)

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
        
        if(err.a == -1) betah.a <- c(0, -2, 0)
        else betah.a <- beta.a + rnorm(3, mean = n^(-err.a), sd = n^(-err.a))
        if(err.b == -1)  betah.b <- c(0, -2, 0)
        else betah.b <- beta.b + rnorm(3, mean = n^(-err.b), sd = n^(-err.b))
        
        bhat <- b.x(betah.b, x1, x2)
        ahat <- a.x(betah.a, x1, x2)
        
        # place them in the right format for drtmle
        Qn <- list(bhat)
        gn <- list(ahat)
        tmle.est <- drtmle(Y=y, A=a, W=x, a_0=1, Qn=Qn, gn=gn, 
                           SL_Qr=SL.lib.drtmle, SL_gr=SL.lib.drtmle)
        
        aipw <- estimator(y, a, ahat, bhat, kern, guard="TRUE")
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
                              tmle.est=tmle.est$drtmle$est,
                              tmle.se=sqrt(tmle.est$drtmle$cov))
        res <- rbind(res, new.res)
      }
    }
  }
}

saveRDS(res, "./dr_inference_sims.RData")


### Check and plot the results ###
res <- readRDS("./dr_inference_sims.RData")
library(tidyr)
library(dplyr)

mytheme <- theme_bw() + 
  theme(axis.text = element_text(size = 30),
        axis.title = element_text(size = 30),
        legend.key.size = unit(1, "cm"),
        legend.text = element_text(size = 30))

# add some redundant information for easier plotting
res <- res %>% 
  mutate(sim_id = seq(n()),
         corrA.se = aipw.se,
         corrB.se = aipw.se,
         corr.se = aipw.se)

res.est <- res %>% 
  select(n, a.err, b.err, sim_id,
         oracle.est, aipw.est, corrA.est, corrB.est, corr.est, tmle.est) %>%
  rename(oracle = oracle.est,
         aipw = aipw.est,
         corrA = corrA.est,
         corrB = corrB.est,
         corr = corr.est,
         tmle = tmle.est) %>%
  pivot_longer(cols = c(oracle, aipw, corrA, corrB, corr, tmle),
               names_to = "method",
               values_to = "estimate") %>%
  group_by(n, a.err, b.err, sim_id)

res.se <- res %>% 
  select(n, a.err, b.err, sim_id,
         oracle.se, aipw.se, corrA.se, corrB.se,
         corr.se, tmle.se) %>%
  rename(oracle = oracle.se,
         aipw = aipw.se,
         corrA = corrA.se,
         corrB = corrB.se,
         corr = corr.se,
         tmle = tmle.se) %>%
  pivot_longer(cols = c(oracle, aipw, corrA, corrB, corr, tmle),
               names_to = "method",
               values_to = "se")
head(res.se)

res.plot <- inner_join(res.se, res.est, 
                  join_by(n == n, a.err == a.err, b.err == b.err, sim_id == sim_id,
                          method == method))
res.plot <- res.plot %>%
  group_by(n, a.err, b.err, method, sim_id) %>%
  mutate(covered = (abs(estimate - truth) / se) <= 1.96)

labels <- c("aipw" = expression(hat(psi)["DR"]),
            "corrA" = expression(hat(psi)["a"]),
            "corrB" = expression(hat(psi)["b"]),
            "corr" = expression(hat(psi)),
            "oracle" = "or", 
            "tmle" = "drtmle")

for(err.a in error.rates.a) {
  for(err.b in error.rates.b) {
    if(err.a == -1 & err.b == -1) next
    if(err.a == -1 & err.b == 0) next
    if(err.a == 0 & err.b == -1) next
    p1 <- ggplot(data = res.plot %>% 
                   filter(n == 2000, a.err == err.a, b.err == err.b)) +
      geom_boxplot(aes(y = sqrt(n) * (estimate - truth), 
                       x = as.factor(method))) +
      scale_x_discrete(labels = labels) +
      geom_hline(yintercept = 0, col = "red") +
      scale_y_continuous(limits = c(-5, 10)) +
      labs(x = "", y = expression(sqrt(n) %*% (estimate - truth))) +
      mytheme
    name <- paste0("./errors_", err.a, "A", "_", err.b, "B.pdf")
    ggsave(p1, filename = name, width = 8, height = 8)
  }
}

res.plot.se <- res.plot %>% 
  filter(n == 2000, a.err == 0.3, b.err == -1, 
         method %in% c("aipw", "corrA", "corrB", "corr", "oracle", "tmle")) %>%
  ungroup()

aipw.true.se <- res.plot.se %>% filter(method == "aipw") %>%
  summarise(true.se = sd(estimate)) %>%
  pull(true.se)
corr.true.se <- res.plot.se %>% filter(method == "corr") %>%
  summarise(true.se = sd(estimate)) %>%
  pull(true.se)
oracle.true.se <- res.plot.se %>% filter(method == "oracle") %>%
  summarise(true.se = sd(estimate)) %>%
  pull(true.se)
drtmle.true.se <- res.plot.se %>% filter(method == "tmle") %>%
  summarise(true.se = sd(estimate)) %>%
  pull(true.se)

p2 <- ggplot(data = res.plot.se %>% 
               filter(method %in% c("aipw", "corr", "oracle", "tmle"))) +
  geom_boxplot(aes(y = se, x = as.factor(method))) +
  scale_x_discrete(labels = c("aipw" = expression(hat(psi)["DR"]),
                              "corr" = expression(hat(psi)),
                              "oracle" = "oracle", 
                              "tmle" = "drtmle")) +
  geom_segment(aes(x = 0.75, xend = 1.25, 
                   y = aipw.true.se, yend = aipw.true.se),
               col = "red", linewidth = 2) +
  geom_segment(aes(x = 1.75, xend = 2.25, 
                   y = corr.true.se, yend = corr.true.se),
               col = "red", linewidth = 2) +
  geom_segment(aes(x = 2.75, xend = 3.25, 
                   y = oracle.true.se, yend = oracle.true.se),
               col = "red", linewidth = 2) +
  geom_segment(aes(x = 3.75, xend = 4.25, 
                   y = drtmle.true.se, yend = drtmle.true.se),
               col = "red", linewidth = 2) +
  labs(x = "", y = "Estimated s.e.") +
  mytheme
p2

res.coverage <- res.plot %>% 
  group_by(n, a.err, b.err, method) %>%
  summarise(coverage = mean(covered, na.rm = TRUE))

labels <- c("aipw" = expression(hat(psi)["DR"]),
            "corrA" = expression(hat(psi)["a"]),
            "corrB" = expression(hat(psi)["b"]),
            "corr" = expression(hat(psi)),
            "oracle" = "oracle", 
            "tmle" = "drtmle")

for(err.a in error.rates.a) {
  for(err.b in error.rates.b) {
    p3 <- ggplot(data = res.coverage %>% filter(a.err == err.a, b.err == err.b)) +
      geom_point(aes(x = n, y = coverage, col = method)) +
      geom_line(aes(x = n, y = coverage, col = method, linetype = method)) +
      scale_color_discrete(labels = labels, name = "") +
      scale_x_continuous(breaks = sample.sizes, trans = "log10") +
      scale_y_continuous(breaks = c(0.5, 0.80, 0.95), limits = c(0.5, 1)) + 
      scale_linetype_discrete(name = "", labels = labels) +
      geom_hline(yintercept = 0.95, col = "black") +
      labs(x = "Sample size", y = "") +
      mytheme
    
    p3
    name <- paste0("./coverage_", err.a, "A", "_", err.b, "B.pdf")
    
    ggsave(p3, filename = name, width = 8, height = 8)
  }
}