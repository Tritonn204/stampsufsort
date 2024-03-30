#pragma once

void SA_IS(unsigned char *s, int *SA, int n, int K, int cs, int level);

void induceSAl(unsigned char *t, int *SA, unsigned char *s, int *bkt, 
               int n, int K, int cs, int level);

void induceSAs(unsigned char *t, int *SA, unsigned char *s, int *bkt, 
               int n, int K, int cs);