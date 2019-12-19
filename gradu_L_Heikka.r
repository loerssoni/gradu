# load up libraries
library(readr)
library(fBasics)
library(boot)
library(dplyr)
library(tidyr)
library(zoo)
library(data.table)
library(roll)
library(DescTools)
library(sandwich)
library(lmtest)

##########################
##### data reading #######
#### and wrangling #######
##########################

#############################
### Read Fama French ########
### portfolio returns #######
#############################

ff6 <- read_csv('ff6_monthly_vw.csv')
ff6[,-1] <- ff6[,-1]/100


ff25 <- read_csv('ff25_monthly_vw.csv')
ff25[,-1] <- ff25[,-1]/100


ind10 <- read_csv('ind10_monthly_vw.csv')
ind10[,-1] <- ind10[,-1]/100


ind30 <- read_csv('ind30_monthly_vw.csv')
ind30[,-1] <- ind30[,-1]/100

######################################
##### Read and wrangle CRSP data   ###
######################################

crsp <- read_table('crsp.txt')
crsp <- crsp[,c(1,2,5,6)]
names(crsp) <- c('permno', 'date', 'mv', 'ret')
crsp$date <- as.Date(as.character(crsp$date), '%Y%m%d')


# set formation period for calculating momentum, these can be changed
# to rerun for alternative strategy specifications in robustness checks


crspset_create <- function(crsp, skip_crsp = 1, horizon_crsp = 12, winsorize = FALSE){
#form momentum variable (right now, filtering missing returns)
  crspset <- crsp %>%
    filter(ret>-1.1)%>%
    group_by(permno)%>%
    mutate(tri = cumprod(1+ret),
           mom = dplyr::lag(tri, 1+skip_crsp)/dplyr::lag(tri, horizon_crsp+1)-1,
           )%>%
    select(-tri)%>%
    filter(!is.na(mom))%>%
    ungroup()%>%
    filter(!is.na(mv))%>%
    group_by(date)%>%
    mutate(mv_m=quantile(mv, 0.5),
           mv_2 = quantile(mv, 0.2))%>%
    ungroup()%>%
    filter(mv >= mv_2)
  if (winsorize == TRUE) {
    crspset <- crspset %>%
       mutate(mom=Winsorize(mom, probs=c(0.05,0.95), na.rm=T))%>%
       mutate(ret=Winsorize(ret, probs=c(0.05,0.95), na.rm=T))
  }
  return(crspset)
}

#for this run, do default settings
crspset <- crspset_create(crsp)

#check how many observations we have
length(unique(crspset2$permno))

# spread data into a wide dataframe with separate columns for return and momentum for each
# permno, used later for the decomposition estimation
pfs<- as.data.frame(dcast(setDT(crspset), date ~ permno, value.var = c('ret', 'mom')))


########################################
##### FULL REALIZED RETURN FOR #########
############ CRSP SAMPLE ###############
########################################

strat_is <- crspset %>%
  group_by(permno)%>%
  #filter(length(ret)>60)%>%
  group_by(date)%>%
  mutate(mom_ew = mean(mom),
         n=length(permno))%>%
  ungroup()%>%
  mutate(w = (mom-mom_ew)/n)%>%
  group_by(date)%>%
  mutate(scl = 2/sum(abs(w)))%>%
  ungroup()

strat_is <- strat_is%>%
  mutate(w = scl* w,
         p_ret= w * ret)


port_ret <- strat_is %>%
  #Optionally filter by period:
  #filter(date > as.Date('19561231', '%Y%m%d'))%>%
  #filter(date >= as.Date('19870101', '%Y%m%d'))%>%
  group_by(date)%>%
  summarise(ret = sum(p_ret),
            abs_check = sum(abs(w)),
            w_check = sum(w))


returns <- cbind(t.test(port_ret$ret*100*12)$estimate, t.test(port_ret$ret*100*12)$statistic)
print(returns)
#a little plot as a sanity check
plot(log(cumprod(1+port_ret$ret))~port_ret$date, type='l', col='red')
crashes <- port_ret$date[which(port_ret$ret < -0.2)];crashes
abline(v = crashes, col='blue', lty='dotted', lwd=0.1)

#######################################################
### Function for calculating realized return to a   ###
### momentum strategy from given set of returns and ### 
### corresponding momentum returns.                 ###
#######################################################
realized_returns <- function(dset, momset, annualize=12){
  n <- ncol(dset)
  #calculate cross-sectional weights and returns
  cs_weights <- (momset - rowMeans(momset))/n
  cs_weights <- 2 * cs_weights / (rowSums(abs(cs_weights)))
  cs_port_ret <- rowSums(cs_weights*dset)
  
  #t-test for percentage returns
  cs_t <- t.test((cs_port_ret))
  cs_stats <- (cbind(annualize*100*cs_t$estimate, cs_t$statistic))
  return(cs_stats)
}

#######################################################
### Function for calculating the decomposition from ###
### given set of returns and corresponding momentum ###
#######################################################

decompose <- function(dset, momset, r_momset, annualize=12){
  n <- ncol(dset)
  #scaling factor
  cs_weights <- ((r_momset - rowMeans(r_momset, na.rm=T))/n)
  #for time-invariant scaling:
  scl <- 2 / mean((rowSums(abs(cs_weights), na.rm=T)))
  
  #gamma_1 and vector of ones
  gamma_1 <- cov(dset, momset, use='pairwise.complete.obs')
  e <- rep(1, n)
  #unconditional means
  mu_d <- colMeans(dset, na.rm=T)
  mu_w <- colMeans(momset, na.rm=T)
  
  
  
  #calculate the components
  c <- scl * annualize * ((-1/n^2) * (t(e) %*% gamma_1 %*% e - sum(diag(gamma_1))))
  o <- scl * annualize * ((n-1)/n^2 * sum(diag(gamma_1)))
  sigma_sq <- scl * annualize * cov(mu_d, mu_w) * (n-1)/n
  e_r <- c + o + sigma_sq
  
  decomp_cs <- cbind(c,o,sigma_sq, e_r)
  colnames(decomp_cs) <- c('Cross-covariances', 'Own-autocovariances', 'Variance', 'Expected returns')
  return(decomp_cs)
}

#########################################################################################
################################ Sampling of CRSP stocks ################################
#########################################################################################


####################################################
## Function for calculating average decomposition ##
## stats, that takes a spread dataframe of stocks ##
## with returns and momentum as separate columns  ##
## for each stock.                                ##
####################################################

random_sampling_crsp <- function(df, win_length=24, by_every=24, samples=100, seed = 69, n=100) {
  ## win_length = length of time window for which full returns are required
  ## by_every = how often to repeat the procedure
  ## samples = how many times the sampling is done for each estimation window
  ## seed = set seed for repeatable results
  ## n = number of stocks that we use for the strategy
  
  #number of total stocks to sample from
  n_stocks <- (ncol(df)-1)/2
  
  
  # make a sequence of indices to use in the loop,
  # according to win_length and by_every
  seq_of_i <- seq(1,nrow(df)-win_length+1, by=by_every)
  if(max(seq_of_i) != nrow(df)-win_length){
     seq_of_i <- c(seq_of_i, nrow(df)-win_length+1)
  }
  
  #dummy data for the results
  cs_results <- matrix(data=NA, nrow=length(seq_of_i), ncol=12)
  
  #incremented variables
  i <- 1 # for the estimation window
  r <- 1 # for row on which to store result
  
  #For each time period in the sequence we do:
  for(i in seq_of_i){
    #store last date of the required horizon as the date
    cs_results[r,1] <- df$date[c(i+win_length-1)] 
    
    #find complete cases in initial window
    data <- df[c(i:(i+win_length-1)),-1]
    cmplt <- complete.cases(t(data[,c((n_stocks+1):(n_stocks*2))]))
    
    #select complete data based on above filtering
    estdata <- data[,c(cmplt, cmplt)]
    data <- df[,c(F,cmplt, cmplt)]
    
    
    #number of stocks  to sample from and average length of return history, store it
    obs <- (ncol(data))/2
    cs_results[r,2] <- obs
    cs_results[r,12] <- mean(apply(data, 2, function(x) length(which(!is.na(x)))))
    
    #dummy data for period results
    period_results <- matrix(data=NA, nrow=samples, ncol=6)
      
    #incremented variable to change the seed and resample
    j <- 1
    
    #from 1 to number of samples repeat procedure 
    for(j in c(1:samples)){
      #sample
      set.seed(seed+j)
      smp <- sample(1:(obs), n, replace=F)
      dset <- data[,c(smp)]
      momset <- data[,c(smp+obs)]
      r_dset <- estdata[,c(smp)]
      r_momset <- estdata[,c(smp+obs)]
      
      #store j:th sample of results using the realized_return and decomposition
      period_results[j,] <- c((decompose(dset, momset, 12)*100), realized_returns(r_dset, r_momset, 12))
    }
    
    #medians of these observations are the observations for the time period
    cs_results[r,c(3:8)] <- apply(period_results, 2, mean)
    
    #t-statistics of these
    t_stats <- c(t.test(period_results[,1])$statistic, t.test(period_results[,2])$statistic,
                 t.test(period_results[,3])$statistic, t.test(period_results[,5])$statistic)
    cs_results[r,c(8:11)] <- t_stats
    
    #increment row,number
    r <- r+1
   #scramble the seed a bit
    seed <- seed+42
    
  }
  
  #tidy it up and return
  cs_results <- as.data.frame(cs_results)
  colnames(cs_results) <- c('date', 'N of stocks', 'Cross-covariances', 'Own-autocovariances',
                            'Variance', 'Expected returns', 'Realized returns',
                            't(C)', 't(O)', 't(mu)','t(R)', 'Avg. length')
  cs_results$date <- as.Date(cs_results$date)
  return(cs_results)
}


#A test run:
stats <- random_sampling_crsp(pfs, win_length=24, by_every=12, samples=500, seed=5, n=50)
apply(stats[,6:7],2,t.test)
round(colMeans(stats[,c(2:7)]), 2)

###############################################
### Standard decomposition for FF data ########
###############################################

returns_FF <- function(dset, annualize = 12, exclude_months= 0, horizon = 12){
  n <- ncol(dset)-1
  dset <- gather(dset, permno, ret, -date)

  momset <- dset %>%
    group_by(permno)%>%
    #filter(!is.na(ret))%>%
    mutate(tri = cumprod(1+coalesce(ret, 0)),
           mom = dplyr::lag(tri, 1+exclude_months)/dplyr::lag(tri, horizon+1)-1,
           group_row = 1:n())%>%
    select(-c(ret, tri))%>%
    ungroup()
  
  dset <- dset %>%
    group_by(permno)%>%
    mutate(group_row = 1:n())
  
  momset <- spread(momset, permno, mom)[-c(1:(horizon+1)),-c(1,2)]
  dset <- spread(dset, permno, ret)[-c(1:(horizon+1)),-c(1,2)]
  
  stats <- realized_returns(dset, momset, annualize)
  return(stats)
}


###function for components and expected returns for FF data
components_FF <- function(dset, annualize = 12, exclude_months= 0, horizon = 12) {
  
  dset <- as.data.frame(dset)
  n <- ncol(dset)-1
  names(dset) <- c('date', 1:n)
  dset <- gather(dset, permno, ret, -date)
  

  momset <- dset %>%
    group_by(permno)%>%
    mutate(tri = cumprod(1+ret),
           mom = dplyr::lag(tri, 1+exclude_months)/dplyr::lag(tri, horizon+1)-1,
           group_row = 1:n())%>%
    select(-c(ret, tri))%>%
    ungroup()
  
  dset <- dset %>%
    group_by(permno)%>%
    mutate(group_row = 1:n())
  
  
  momset <- spread(momset, permno, mom)[-c(1:(horizon+1)),-c(1,2)]
  dset <- spread(dset, permno, ret)[-c(1:(horizon+1)),-c(1,2)]
  #dset <- (apply(dset, 2, FUN = function(x) Winsorize(x, probs=c(0.05, 0.95), na.rm=T)))
  #momset <- (apply(momset, 2, FUN = function(x) Winsorize(x, probs=c(0.05, 0.95), na.rm=T)))
  stats <- decompose(dset, momset, momset, annualize=annualize)
  return(stats)
}



#functions for some test tables on ff-data
tables_ret <- function (ann, skp, hrz) {
  x <- rbind(
  returns_FF(ff62, ann, skp, hrz),
  returns_FF(ff252, ann, skp, hrz),
  returns_FF(ind102, ann, skp, hrz),
  returns_FF(ind302, ann, skp, hrz))
  rownames(x) <- c('FF6', 'FF25', 'Ind10','Ind30')
  colnames(x) <- c('Return','T-stat')
  return(data.frame(x))
}


##winsorized returns 
ff62 <- ff6
ff62[,-1] <- matrix(Winsorize(stack(ff6[,-1])[,1], probs=c(0.005,0.995)), ncol=6)

ff252 <- ff25
ff252[,-1] <- matrix(Winsorize(stack(ff25[,-1])[,1], probs=c(0.005,0.995)), ncol=25)

ind102 <- ind10
ind102[,-1] <- matrix(Winsorize(stack(ind10[,-1])[,1], probs=c(0.005,0.995)), ncol=10)

ind302 <- ind30
ind302[,-1] <- matrix(Winsorize(stack(ind30[,-1])[,1], probs=c(0.005,0.995)), ncol=30)

tables_comp <- function (ann, skp, hrz) {
  x <- rbind(100*components_FF(ff62, ann, skp, hrz),
             100*components_FF(ff252, ann, skp, hrz),
             100*components_FF(ind102, ann, skp, hrz),
             100*components_FF(ind302, ann, skp, hrz))
  rownames(x) <- c('FF6', 'FF25', 'Ind10','Ind30')
  return(x)
  }

#a couple of tests on FF data
round(tables_ret(12, 1, 12),2)
round(tables_comp(12, 1, 12), 2)



###########################################################################
###################### INVESTMENT STRATEGY -BASED    ######################
###################### DECOMPOSITION FOR CRSP SAMPLE ######################
###########################################################################

crsp <- read_table('crsp.txt')
crsp <- crsp[,c(1,2,5,6)]
names(crsp) <- c('permno', 'date', 'mv', 'ret')
crsp$date <- as.Date(as.character(crsp$date), '%Y%m%d')

crspset <- crspset_create(crsp)

#Function for computing strategy based decomposition for individual stocks and portfolio data
#This part is rerun for different specifications in robustness checks
strat_decompose <- function(dset, port=F, skip_crsp=1, horizon_crsp=12){
  
  #the portfolio datasets need some additional wrangling here
  if(port==T){
    
    dset <- gather(dset, permno, ret, -date)
    dset <- dset %>%
      group_by(permno)%>%
      mutate(tri = cumprod(1+coalesce(ret, 0)),
             mom = dplyr::lag(tri, 1+skip_crsp)/dplyr::lag(tri, horizon_crsp+1)-1,
             group_row = 1:n())%>%
      filter(!is.na(mom))%>%
      select(-tri, -group_row)%>%
      ungroup()
  }
  
  strat_is <- dset %>%
    group_by(permno)%>%
    mutate(ind = row_number(),
           #different specifications for mu estimate:
           
           #in-sample:
           #mu=mean(mom)
           #forward-looking mean:
           #mu = lead(rev(roll_mean(as.matrix(rev(mom)), 1100, min_obs=24)), 13),
           #past mean:
           mu = lag(roll_mean(as.matrix(mom), 120, min_obs=120), 1),
           #past+forward-looking out-of-sample:
           #mu = (ind+16)/(max(ind)+16)*mu2 + (1-(ind+16)/(max(ind)+16))*mu
    )%>%
    #require longer history:
    #filter(length(ret)>48)%>%
    filter(!is.na(mu))%>%
    ungroup()
  
  if(port!=T){
    
    strat_is <- strat_is %>%
      filter(!is.na(mv))%>%
      group_by(date)%>%
      mutate(mv_m=quantile(mv, 0.5),
             mv_2 = quantile(mv, 0.2))%>%
      ungroup()%>%
      filter(mv>=mv_2)
    
  }
  
  ####
  strat_is <- strat_is %>%
    group_by(date)%>%
    mutate(mom_e = mean(mom),
           n=length(permno),
           mu_e = mean(mu))%>%
    ungroup()%>%
    mutate(w = (mom-mom_e)/n,
           w_o = (((n-1)/n)*(mom-mu))/n,
           w_c = -(1/n)*(mom_e - mu_e - (1/n)*(mom-mu)),
           w_ts = (mom-mom-(mom_e-mu_e)),
           w_sigma = (mu-mu_e)/n
    )%>%
    
    group_by(date)%>%
    mutate(scl = 2/sum(abs(w)),
           #scl_o = ifelse(sum(w_o)>0, 1/sum(ifelse(w_o>0, w_o, 0)), 1/sum(ifelse(w_o<0, -w_o, 0))),
           #scl_c = ifelse(sum(w_c)>0, 1/sum(ifelse(w_c>0, w_c, 0)), 1/sum(ifelse(w_c<0, -w_c, 0))),
           #scl_c = sum(w_c),
           #scl_o = ifelse(sum(w_o)>0, 1/sum(ifelse(w_o>0, w_o, 0)), 1/sum(ifelse(w_o<0, -w_o, 0))),
           scl_s = 2/sum(abs(w_sigma)),
           scl_o = 1/sum(abs(w_o)),
           scl_c = 1/sum(abs(w_c)),
           scl_ts = 2/sum(abs(w_ts))
    )%>%
    #select(-mv_m)%>%
    ungroup()#%>%
  #mutate(scl_c = 1, scl_o=1, scl_s=1, scl=1)
  
  
  port_ret <- strat_is%>%
  #alternatively filter different time periods
    #filter(date > as.Date('19391231', '%Y%m%d'))%>%
    #filter(date >= as.Date('19901231', '%Y%m%d'))%>%
    #filter(date > 194512)%>%
    mutate(e_ret= scl * w * ret,
           o_ret= scl_o * w_o * ret,
           c_ret= scl_c * w_c * ret,
           sig_ret= scl_s * w_sigma * ret,
           ts_ret=scl_ts*w_ts*ret)%>%
    group_by(date)%>%
    summarise(
      Er = sum(e_ret),
      C = sum(c_ret),
      O = sum(o_ret),
      Sigma = sum(sig_ret),
      ts = sum(ts_ret),
      abs_check = sum(abs(scl_o*w_o)),
      w_check = sum(scl_o*w_o),
      w_check_c = sum(scl_c*w_c)
    )%>%
    ungroup()
  
  
  x <- cbind(rbind(t.test(port_ret$Er*100*12)$estimate,
                   t.test(port_ret$C*100*12)$estimate,
                   t.test(port_ret$O*100*12)$estimate,
                   t.test(port_ret$Sigma*100*12)$estimate),
             rbind(t.test(port_ret$Er*100*12)$statistic,
                   t.test(port_ret$C*100*12)$statistic,
                   t.test(port_ret$O*100*12)$statistic,
                   t.test(port_ret$Sigma*100*12)$statistic)
  )
  
  
  rownames(x) <- c('E(r)', 'C','O','Sigma')
  colnames(x) <- c('Estimate', 'T-stat')
  
  print(summary(port_ret))
  print(round(t(x),2))
  print(round(cor(port_ret[,c(2:5)], use='pairwise.complete.obs'), 2))
  return(port_ret)
}

port_ret <- strat_decompose(crspset, port=F, 1,12)

#Function for return regressions with NeweyWest corrected errors
lm_results <- function(dset){
  cor_mat <- cor(dset[,c(2:5)], use='pairwise.complete.obs')
  o <- coeftest(lm(dset$Er ~ (dset$O)), NeweyWest(lm(dset$Er ~ (dset$O))))
  o <- rbind( t(o[,1]), t(o[,3]))
  o <- cbind(o[,1], matrix(NA, 2, 1), o[,2], matrix(NA, 2,1))
  o[1,1] <- o[1,1]*12*100
  
  c <- coeftest(lm(dset$Er ~ dset$C), NeweyWest(lm(dset$Er ~ dset$C)))
  c <- cbind(rbind( t(c[,1]), t(c[,3])), matrix(NA, 2, 2))
  c[1,1] <- c[1,1]*12*100
  
  s <- coeftest(lm(dset$Er ~ dset$Sigma), NeweyWest(lm(dset$Er ~ dset$Sigma)))
  s <- rbind( t(s[,1]), t(s[,3]))
  s <- cbind(s[,1], matrix(NA, 2, 2), s[,2])
  s[1,1] <- s[1,1]*12*100
  
  os <- coeftest(lm(dset$O ~ dset$Sigma), NeweyWest(lm(dset$O ~ dset$Sigma)))
  os <- rbind( t(os[,1]), t(os[,3]))
  os <- cbind(os[,1], matrix(NA, 2, 2), os[,2])
  os [1,1] <- os[1,1]*12*100
  
  x <- rbind(c,o,s, os)
  
  colnames(x) <- c('Intercept','C','O','Sigma')
  rownames(x) <- c('EronC','-','EronO','-','EronSigma','-', 'OonSigma','-')
  return(x)
}


round(lm_results(port_ret),2)



#Plot cumulative strategy returns
plot_cumret <- function(x){
  plot(x$date,log(cumprod(1+x$Er)), type='l', lty=2, ylim=c(-5,10), lwd=2, ylab='Cumulative Return',xlab='Year')
  lines(x$date, log(cumprod(1+x$O)), col='red',lwd=2, lty=1)
  lines(x$date,log(cumprod(1+x$C)),col='blue',lwd=2, lty=1)
  lines(x$date,log(cumprod(1+x$Sigma)),col='green',lwd=2, lty=1)
  abline(h=0)
  legend(x=as.Date('19301231', '%Y%m%d'), y=9, legend=c('O', 'C','Sigma', 'E(R)'),
         col=c('red','blue', 'green', 'black'), lty=c(1,1,1,2), lwd=2, cex=1)
  abline(h=0)
}
plot_cumret(port_ret)

#Plot rolling returns/contributions
plot_rolling_contributions <- function(x, window){
  dates <- port_ret$date
  er <- roll_mean(as.matrix(x$Er*12*100), window, min_obs=window)
  o <- roll_mean(as.matrix(x$O*12*100), window, min_obs=window)
  c <- roll_mean(as.matrix(x$C*12*100), window, min_obs=window)
  s <- roll_mean(as.matrix(x$Sigma*12*100), window, min_obs=window)
  plot(dates[((window/2):(length(dates)-(window/2)-1))], c[-c(1:window)], type='l', col='blue',
       lty=1, ylim=c(-25, 20), xlab='Year', ylab='Return')
  lines(dates[((window/2):(length(dates)-(window/2)-1))], o[-c(1:window)], col='red', lty=1)
  #lines(dates[((window/2):(length(dates)-(window/2)-1))], c[-c(1:window)], col='blue', lty=2)
  lines(dates[((window/2):(length(dates)-(window/2)-1))], s[-c(1:window)], col='green', lty=1)
  abline(h=0)
  legend((min(dates)+3000), -10, legend=c('O','C', 'Sigma'),
         col=c('red', 'blue','green'), lty=c(1,1,1), cex=1)
  
}
plot_rolling_contributions(port_ret, 60)

#######################################################################
######################## BOOTSTRAP EXPERIMENT #########################
#######################################################################

###################################
##### CRSP SAMPLE BOOTSTRAP #######
###################################

#function to compute crsp strategy based decomposition
crsp_returns <- function(dset, skip_crsp, horizon_crsp, port=T){
  bootdata <- dset %>%
    filter(!is.na(ret))%>%
    filter(ret>-1.1)%>%
    group_by(permno)%>%
    mutate(tri = cumprod(1+ret),
           mom = dplyr::lag(tri, 1+skip_crsp)/dplyr::lag(tri, horizon_crsp+1)-1
    )%>%
    select(-tri)%>%
    
    filter(!is.na(mom))%>%
    ungroup()
  
  bs <- bootdata%>%
    group_by(permno)%>%
    mutate(o = cov(mom, ret),
           mu = mean(ret),
           mumom = mean(mom))%>%
    filter(!is.na(o))%>%
    ungroup()%>%
    group_by(date)%>%
    summarise(o=mean(o), n=length(permno), mu=cov(mu, mumom))
  
  covar <- sum(bs$n*(bs$o))/sum(bs$n)
  mu <- sum(bs$n*(bs$mu))/sum(bs$n)
  
  
  strat_is <- bootdata %>%
    group_by(date)%>%
    mutate(mom_ew = mean(mom),
           r_ew = mean(ret),
           n=length(permno))%>%
    ungroup()%>%
    mutate(w = (mom-mom_ew)/n)%>%
    group_by(date)%>%
    mutate(scl = 2/sum(abs(w)),
           r_ew = mean(ret))%>%
    ungroup()
  
  ew <- strat_is%>%
    group_by(date)%>%
    summarise(mean(mom_ew), mean(r_ew))
  
  strat_is <- strat_is%>%
    mutate(w = scl* w,
           p_ret= w * ret)
  
  port_ret <- strat_is %>%
    group_by(date)%>%
    summarise(ret = sum(p_ret),
              abs_check = sum(abs(w)),
              w_check = sum(w))
  
  t_stats <- t.test(port_ret$ret*100*12)
  x <- cbind(t_stats$estimate, t_stats$statistic, covar*12*100, mu*12*100)
  rownames(x) <- ''
  colnames(x) <- c('Ret', 'T', 'Autocov', 'Sigma')
  return(x)
}

reps <- 500
boot_stats <- matrix(NA, reps, 4)

# loop to create a scarmbled bootstrap sample and compute the strategy-based decomposition 
# the amount of replications is set by reps. Individual stocks are sampled separately,
# and the contemporaneous covariance structure is lost
for(i in 1:reps){
  rets <- crsp %>%
    filter(ret>-1)%>%
    filter(!is.na(mv))%>%
    group_by(date)%>%
    mutate(mv_m=quantile(mv, 0.5),
           mv_2 = quantile(mv, 0.2))%>%
    ungroup()%>%
    filter(mv >= mv_2)%>%
    group_by(permno)%>%
    #change replace F/T for sampling Without or with replacement
    sample_frac(., 1, replace=F)%>%
    ungroup()%>%
    mutate(ret=Winsorize(ret, probs=c(0.01,0.99), na.rm=T))%>%
    select(ret)
  
  data <- crsp %>%
    filter(ret>-1)%>%
    filter(!is.na(mv))%>%
    group_by(date)%>%
    mutate(mv_m=quantile(mv, 0.5),
           mv_2 = quantile(mv, 0.2))%>%
    ungroup()%>%
    filter(mv >= mv_2)
  
  data$ret <- rets$ret
  
  boot_stats[i,] <- crsp_returns(data, 1, 12, port=F)
  
}

colnames(boot_stats) <- c('Ret', 'T', 'Autocov', 'Sigma')

#wrangle the table:
bootstats <- cbind(t.test(boot_stats[,1])$estimate, t.test(boot_stats[,1])$statistic,
                   t.test(boot_stats[,3])$estimate, t.test(boot_stats[,3])$statistic)
colnames(bootstats) <- c('Return', 'T-stat', 'Autocovariance', 'T-stat')
rownames(bootstats) <- ''
bootstats


##############################
## Bootstrap for portfolios ##
##############################

#estimate bootstrap for FF data, maintaining contemporaneous covariance structure
estimate_boot_FF <- function(dset, reps=500){
  boot_stats <- matrix(NA, reps, 4)
  for(i in 1:reps){
    data <- sample_frac(dset, 1, replace=F) 
    data$date <- dset$date
    boot_stats[i,] <- cbind(t(components_FF(data,12,1,12)[,c(1:3)]*100),returns_FF(data, 12, 1, 12)[,1])
  }
  #return((boot_stats))
  return(cbind(rbind(t.test(boot_stats[,1])$estimate, t.test(boot_stats[,1])$statistic),
               rbind(t.test(boot_stats[,2])$estimate, t.test(boot_stats[,2])$statistic),
               rbind(t.test(boot_stats[,3])$estimate, t.test(boot_stats[,3])$statistic),
               rbind(t.test(boot_stats[,4])$estimate, t.test(boot_stats[,4])$statistic)
               
  ))
}

#Run and create a table for the FF data
FF_boot_stats <- rbind(estimate_boot_FF(ff6, 500),
                       estimate_boot_FF(ff25, 500),
                       estimate_boot_FF(ind10, 500),
                       estimate_boot_FF(ind30, 500)
                       
)
colnames(FF_boot_stats) <- c('C','O','Var','Ret');rownames(FF_boot_statsT) <- c('ff6', 'ff25','ind10','ind30')
round(FF_boot_stats, 2)

