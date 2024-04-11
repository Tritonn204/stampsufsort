#include "theory.h"
#include <iostream>
#include <algorithm>
#include <unordered_map>
#include "divsufsort.h"
#include "sais.h"
#include "libsais.h"
#include <filesystem>
#include <fstream>
#include <set>
#include <inttypes.h>
#include <chrono>
#include <random>

/*
 * Template Generation for SAIS Algorithm Optimization
 *
 * This program generates templates for datasets used in the SAIS (Suffix Array Induced Sorting) algorithm.
 * The templates are designed to optimize the algorithm by leveraging the specific characteristics and patterns
 * present in the datasets.
 *
 * The main idea behind the optimization is to identify and store the modified byte ranges, offsets, and byte 31
 * offsets for each chunk in the dataset. By using this template data, the SAIS algorithm can be enhanced to
 * avoid unnecessary memory accesses and computations, leading to faster suffix array construction.
 *
 * The program takes a dataset, its size, and the chunk size as input. It then processes the dataset chunk by
 * chunk, comparing each chunk with its previous chunk to identify the modified bytes and their offsets.
 *
 * The template data consists of three main components:
 * 1. Modified Byte Ranges: Stores the first and last modified byte indexes for each modified chunk.
 * 2. Modified Byte Offsets: Stores the offsets of the modified bytes within the identified ranges.
 * 3. Byte 31 Offsets: Stores the offset of byte 31 for each chunk, as it is assumed to be modified nearly 100%
 *    of the time.
 *
 * The generated template data can be used to create an LMS (Leftmost S-Type) suffix "stamp" in the SAIS algorithm.
 * Instead of processing the entire dataset, the algorithm can focus on updating the LMS suffixes only for the
 * modified bytes, using the stored offsets. This selective update approach reduces unnecessary memory accesses
 * and computations, resulting in improved performance.
 *
 * To integrate this optimization into the SAIS algorithm, the following steps can be taken:
 * 1. Generate the template data using this program for the input dataset.
 * 2. Modify the SAIS algorithm to utilize the template data during suffix array construction.
 * 3. When processing each chunk, use the stored modified byte ranges to identify the bytes that need to be updated.
 * 4. Apply the corresponding offsets from the modified byte offsets to update the LMS suffixes for those bytes.
 * 5. Update byte 31 using the stored byte 31 offsets for each chunk.
 * 6. Proceed with the rest of the SAIS algorithm using the optimized LMS suffix array.
 *
 * By leveraging the template data and optimizing the SAIS algorithm, the suffix array construction process can be
 * accelerated, especially for datasets with specific patterns and characteristics like the ones used in this program.
 *
 * Note: The effectiveness of this optimization approach may vary depending on the specific dataset and the SAIS
 * algorithm implementation. It is recommended to benchmark and profile the optimized algorithm to measure the actual
 * performance gains achieved.
 */

unsigned char mask[]={0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01};
#define lcmget(i) ( (lcmsuf[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define lcmset(i, b) lcmsuf[(i)/8]=(b) ? (mask[(i)%8]|lcmsuf[(i)/8]) : ((~mask[(i)%8])&lcmsuf[(i)/8])

#define tget_local(i) ( (tloc[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define tset_local(i, b) tloc[(i)/8]=(b) ? (mask[(i)%8]|tloc[(i)/8]) : ((~mask[(i)%8])&tloc[(i)/8])

#define tget_global(i) ( (t_global[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define tset_global(i, b) t_global[(i)/8]=(b) ? (mask[(i)%8]|t_global[(i)/8]) : ((~mask[(i)%8])&t_global[(i)/8])

#define lget(i) ( (lms[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define lset(i, b) lms[(i)/8]=(b) ? (mask[(i)%8]|lms[(i)/8]) : ((~mask[(i)%8])&lms[(i)/8])

#define lget_global(i) ( (lms_global[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define lset_global(i, b) lms_global[(i)/8]=(b) ? (mask[(i)%8]|lms_global[(i)/8]) : ((~mask[(i)%8])&lms_global[(i)/8])

#define isLMS_global(i) (i>0 && tget_global(i) && !tget_global(i-1))

int cmp(unsigned char x, unsigned char y){ 
   return (x==y)?0:(x>y)?1:-1; 
}

// TODO : Reverse chunk iteration direction. Video I watched was wrong

// Function to generate the template for a given dataset
void generateTemplate_SAIS(const unsigned char* data, int dataSize, int chunkSize, int modSize) {
  std::vector<std::pair<int, int>> modifiedByteRanges;
  std::vector<int> modifiedByteOffsets;
  std::vector<int> chunkTipOffsets;
  std::unordered_map<std::string, LMSInfo> lmsMap;

  int buckets[256] = {0};
  int heads[256] = {0};
  int tails[256] = {0};
  int headsIdx[256] = {0};
  int tailsIdx[256] = {0};

  int buckets_d[256][256] = {0};
  int heads_d[256][256] = {0};
  int tails_d[256][256] = {0};
  int headsIdx_d[256][256] = {0};
  int tailsIdx_d[256][256] = {0};

  unsigned char firstChunk[chunkSize];
  unsigned char finalChunk[chunkSize];
  unsigned char runningChunk[chunkSize];


  int SA[dataSize+1];
  std::fill_n(SA, dataSize+1, -1);

  std::vector<int> T;
  std::vector<int> offsets;

  int LMSlen[dataSize+1];
  std::fill_n(LMSlen, dataSize+1, -1);
    
  std::vector<int> LMSledger;
  std::vector<int> LCP;

  // bool isLMS_global[dataSize+1];
  // std::fill_n(isLMS_global, dataSize+1, false);
  // bool sTypes_global[dataSize+1];
  // std::fill_n(sTypes_global, dataSize+1, false);

  int IS_L[dataSize+1];
  std::fill_n(IS_L, dataSize+1, -1);
  int IS_S[dataSize+1];
  std::fill_n(IS_S, dataSize+1, -1);

  int LMS_sortedIdx[dataSize+1];
  std::fill_n(LMS_sortedIdx, dataSize+1, -1);

  bool modMask[chunkSize];
  std::fill_n(modMask, chunkSize, false);

  // bool sTypes[chunkSize+1];
  // std::fill_n(sTypes, chunkSize, false);
  // bool isLMS[chunkSize+1];
  // std::fill_n(isLMS, chunkSize, false);

  unsigned char *lms=(unsigned char *)malloc((chunkSize+1)/8+1); // LMS tracking array in bits, per-chunk
  unsigned char *lms_global=(unsigned char *)malloc((dataSize+1)/8+1); // LS-type array in bits, globally
  unsigned char *tloc=(unsigned char *)malloc((chunkSize+1)/8+1); // LS-type array in bits, per-chunk
  unsigned char *t_global=(unsigned char *)malloc((dataSize+1)/8+1); // LS-type array in bits, globally

  memset(lms, 0, (chunkSize+1)/8+1);
  memset(tloc, 0, (chunkSize+1)/8+1);
  memset(lms_global, 0, (dataSize+1)/8+1);
  memset(t_global, 0, (dataSize+1)/8+1);

  tset_global(dataSize-1, 0);
  tset_global(dataSize, 1);

  std::vector<int> chunkLMS;
  chunkLMS.reserve(chunkSize);

  int numChunks = dataSize / chunkSize;

  for (int i = 0; i < chunkSize; i++) {
    buckets[data[i]]++;
    firstChunk[i] = data[i];
  }

  modifiedByteRanges.push_back(std::make_pair(-1, -1));
  chunkTipOffsets.push_back(0);

  for (int chunk = 1; chunk < numChunks; chunk++) {
      const unsigned char* prevChunk = data + (chunk - 1) * chunkSize;
      const unsigned char* currChunk = data + chunk * chunkSize;

      int pos1 = -1;
      int pos2 = -1;

      for (int i = 0; i < chunkSize-1; i++) {
          buckets[currChunk[i]]++;
          if (currChunk[i] != prevChunk[i]) {
              if (pos1 == -1) {
                  pos1 = i;
              }
              if (pos1 != -1 && i <= pos1+modSize) pos2 = i;
          }
      }

      if (pos1 != -1) {
          modifiedByteRanges.push_back(std::make_pair(pos1, pos2));

          for (int i = pos1; i <= pos2; i++) {
              int offset = currChunk[i] - prevChunk[i];
              modifiedByteOffsets.push_back(offset);
          }
      } else {
          modifiedByteRanges.push_back(std::make_pair(-1, -1));
      }

      buckets[currChunk[chunkSize-1]]++;

      int tipOffset = currChunk[chunkSize-1] - prevChunk[chunkSize-1];
      chunkTipOffsets.push_back(tipOffset);
  }

  // for (int i = 0; i < dataSize-1; i++) {
  //   buckets_d[data[i]][data[i+1]]++;
  // }

  int s = 1; // Leave room for terminator at start
  for (int i = 0; i < 256; i++) {
    heads[i] = s;
    headsIdx[i] = s;
    tails[i] = s + buckets[i]-1;
    tailsIdx[i] = s + buckets[i]-1;
    s += buckets[i];
  }

  // // Print the template data
  // std::cout << "Modified Byte Ranges:" << std::endl;
  // for (const auto& range : modifiedByteRanges) {
  //     std::cout << "[" << range.first << ", " << range.second << "]" << std::endl;
  // }

  // // std::cout << "\nModified Byte Offsets:" << std::endl;
  // // for (int offset : modifiedByteOffsets) {
  // //     std::cout << offset << " ";
  // // }
  // // std::cout << std::endl;

  // std::cout << "\nChunk Tip Offsets:" << std::endl;
  // for (int offset : chunkTipOffsets) {
  //     std::cout << offset << " ";
  // }
  // std::cout << std::endl;

  tset_local(chunkSize-1, 0);
  lset(chunkSize-1, false);
  tset_local(chunkSize, 1);
  lset(chunkSize, true);
  
  int c;
  for (int i = dataSize+1; i -- > dataSize - chunkSize;) {
    finalChunk[i%chunkSize] = data[i];
    c = cmp(data[i], data[i+1]);
    if (i < dataSize-1) tset_local(i%chunkSize, c < 0 ? true : c == 0 ? tget_local(i%chunkSize+1) : 0); 
    
    if (i < dataSize-1 && !tget_local(i%chunkSize) && tget_local(i%chunkSize+1)) {
      chunkLMS.push_back(i%chunkSize+1);
      lset(i%chunkSize+1, 1);
      // isLMS_global[i%chunkSize+1] = true;
    }
  }

  // std::cout << "\nFinal chunk suffix types" << std::endl;
  // for (int i = 0; i < chunkSize; i++) {
  //     std::cout << (tget_local(i) ? "S " : "L ");
  // }
  // std::cout << std::endl;

  // std::cout << "\nFinal chunk LMS suffixes" << std::endl;
  // for (int suf : chunkLMS) {
  //     std::cout << suf << " ";
  // }
  // std::cout << std::endl;

  // not yet implemented, infer the LMS suffixes when placing them in their buckets from right-to-left
  // inference takes advantage of the patterns in the input data

  std::copy(finalChunk, finalChunk+chunkSize, runningChunk);
  int offIdx = modifiedByteOffsets.size()-1;
  unsigned char nextUp = 0;
  bool nextType = false;

  // printf("numchunks: %d\n", numChunks);
  // printf("data 46: 0x%02X\n", data[46]);
  LMSledger.push_back(dataSize);

  auto start = std::chrono::steady_clock::now();

  int i = 0, j = 0;
  tset_global(dataSize-1, 0); tset_global(dataSize, 1); // the sentinel must be in s1, important!!!
  for(i=dataSize-2; i>=0; i--) tset_global(i, (data[i]<data[i+1] || (data[i]==data[i+1] && tget_global(i+1)==1))?1:0);

  for(i=dataSize-1; i>=0; i--)
  {
    if(i>0 && tget_global(i) && !tget_global(i-1)) {
      SA[tailsIdx[data[i]]]=i;
      tailsIdx[data[i]]--;
    }
  }  
  SA[0] = dataSize;

  // printf("\n");

  // std::cout << "After LMS sort" << std::endl;
  // for (int i = 0; i < dataSize+1; i++) {
  //     std::cout << SA[i] << ", ";
  // }
  // std::cout << std::endl;
  // printf("\n");

  // // Induce terminator L suffix
  // SA[headsIdx[data[dataSize-1]]] = dataSize-1;
  // headsIdx[data[dataSize-1]]++;
  // if (!tget_global(dataSize-2)) IS_L[dataSize-1] = data[dataSize-2];
  // else IS_S[dataSize-1] = data[dataSize-2];

  // auto start2 = std::chrono::steady_clock::now();
  for (i = 0; i < dataSize+1; i++){
    if (SA[i] <= 0) continue;
    j = SA[i]-1;
    if (!tget_global(j)) {
      SA[headsIdx[data[j]]] = j;
      headsIdx[data[j]]++;
    }
  }
  // auto end2 = std::chrono::steady_clock::now();
  // auto time2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2-start2);

  // printf("My L inducing took %.6f seconds\n", (double)time2.count()/1000000000.0);


  // std::cout << "After L-R L-inducing" << std::endl;
  // for (int i = 0; i < dataSize+1; i++) {
  //     std::cout << SA[i] << ", ";
  // }
  // std::cout << std::endl;
  // printf("\n");

  // Induce S-type suffixes
  std::copy(tails, tails+256, tailsIdx); // Reset the back-of-bucket indexes to their original values
  for (i = dataSize+1; i -- > 0;){
    if (SA[i] <= 0) continue;
    j = SA[i]-1;
    if (tget_global(j)) {
      SA[tailsIdx[data[j]]] = j;
      tailsIdx[data[j]]--;
    } 
  }

  // std::cout << "After R-L S-inducing" << std::endl;
  // for (int i = 0; i < dataSize+1; i++) {
  //     std::cout << SA[i] << ", ";
  // }
  // std::cout << std::endl;
  // printf("\n");

  int n1 = 0;
  for (i = 0; i < dataSize+1; i++) {
    if (SA[i]>0 && tget_global(SA[i]) && !tget_global(SA[i]-1)) SA[n1++] = SA[i];
  }

  std::fill_n(SA+n1, dataSize+1-n1, -1);

  // std::cout << "After LMS Packing" << std::endl;
  // for (int i = 0; i < dataSize+1; i++) {
  //     std::cout << SA[i] << ", ";
  // }
  // std::cout << std::endl;


  int name = 0;
  int lastLMS = -1;
  for (i = 0; i < n1; i++) {
    int pos = SA[i]; bool diff = false;
    for(int d=0; d<dataSize+1; d++)
      if(lastLMS==-1 || pos+d==dataSize || lastLMS+d==dataSize ||
          data[pos+d]!=data[lastLMS+d] ||
          tget_global(pos+d)!=tget_global(lastLMS+d))
      { diff=true; break; }
      else
        if(d>0 && ((tget_global(pos+d) && !tget_global(pos+d-1)) || (tget_global(lastLMS+d) && !tget_global(lastLMS+d-1))))
          break;

    if(diff) 
      { name++; lastLMS=pos; }
	  pos=pos/2; //(pos%2==0)?pos/2:(pos-1)/2;
    SA[n1+pos]=name-1;
  }

  for(i=dataSize, j=dataSize; i>=n1; i--)
	  if(SA[i]!=-1) SA[j--]=SA[i];

  // s1 is done now
  int *SA1=SA, *s1=SA+dataSize+1-n1;

  // std::cout << "\nS1 is ready" << std::endl;
  // for (int i = 0; i < dataSize+1; i++) {
  //     std::cout << SA1[i] << ", ";
  // }
  // std::cout << std::endl;
  // printf("\n");

  bool ready = false;

  static double redu_ratio=0;
  static long sum_n=0, sum_n1=0;

  // fprintf(stderr, "\nReduction ratio: %.2lf\n", (double)n1/(dataSize+1));
  redu_ratio += (double)n1/(dataSize+1);
  sum_n1+=n1; sum_n+=(dataSize+1);
  if (name < n1) {
    // printf("name: %d\n", name);
    SA_IS((unsigned char*)s1, SA1, n1, name-1, sizeof(int), 1);
  } else {
    ready = true;
    // printf("level 0, n1 = %d\n", n1);
    for(i=0; i<n1; i++) SA1[s1[i]] = i;
    // std::cerr << std::endl << "Recusion ends";
    // fprintf(stderr, "\nMean reduction ratio over iterations: %.2lf", redu_ratio);
    // fprintf(stderr, "\nMean reduction ratio over characters: %.2lf", (double)sum_n1/sum_n);
  }
  // printf("\n");

  std::copy(heads, heads+256, headsIdx); // Reset the back-of-bucket indexes to their original values
  std::copy(tails, tails+256, tailsIdx); // Reset the back-of-bucket indexes to their original values

  // getBuckets(s, bkt, n, K, cs, true); // find ends of buckets
  // j=0;
  // for(i=1; i<n; i++)
  //   if(isLMS(i)) s1[j++]=i; // get p1
  // for(i=0; i<n1; i++) SA1[i]=s1[SA1[i]]; // get index in s1
  // for(i=n1; i<n; i++) SA[i]=EMPTY; // init SA[n1..n-1]
  // for(i=n1-1; i>=0; i--) {
	//   j=SA[i]; SA[i]=EMPTY;
	//   if(level==0 && i==0)
  //         SA[0]=n-1;
  //     else
  //         SA[bkt[chr(j)]--]=j;
  // }

  j = 0;
  for (i = 1; i < dataSize+1; i++) {
    if (i>0 && tget_global(i) && !tget_global(i-1)) s1[j++]=i;
  }

  for (i = 0; i < n1; i++) SA1[i]=s1[SA1[i]];
  std::fill_n(SA+n1, dataSize+1-n1, -1);

  // std::cout << "Before re-adding" << std::endl;
  // for (int i = 0; i < dataSize+1; i++) {
  //     std::cout << SA1[i] << ", ";
  // }
  // printf("\n");

  for (i = n1-1; i >= 0; i--) {
    j = SA[i]; SA[i] = -1;
	  if(i==0)
          SA[0]=dataSize;
      else {
          SA[tailsIdx[data[j]]]=j;
          tailsIdx[data[j]]--;
      }
  }


  // Induce L-type suffixes
  for (i = 0; i < dataSize+1; i++){
    if (SA[i] <= 0) continue;
    j = SA[i]-1;
    if (!tget_global(j)) {
      SA[headsIdx[data[j]]] = j;
      headsIdx[data[j]]++;
    }
  }

  // std::cout << "After L-R L-inducing" << std::endl;
  // for (int i = 0; i < dataSize+1; i++) {
  //     std::cout << SA[i] << ", ";
  // }
  // std::cout << std::endl;
  // printf("\n");

  // Induce S-type suffixes
  std::copy(tails, tails+256, tailsIdx); // Reset the back-of-bucket indexes to their original values
  for (i = dataSize+1; i -- > 0;){
    if (SA[i] <= 0) continue;
    j = SA[i]-1;
    if (tget_global(j)) {
      SA[tailsIdx[data[j]]] = j;
      tailsIdx[data[j]]--;
    } 
  }

  auto end = std::chrono::steady_clock::now();
  auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  printf("My old method took %.6f seconds\n", (double)time.count()/1000000000.0);

  // std::cout << "Final" << std::endl;
  // for (int i = 1; i < dataSize+1; i++) {
  //     std::cout << SA[i] << ", ";
  // }
  // std::cout << std::endl;
  // printf("\n");

  // int DSS_SA[dataSize];
  // int bA[256];
  // int bB[256*256];
  // divsufsort(data, DSS_SA, dataSize, bA, bB);

  // std::cout << "\nValidated Suffix Array" << std::endl;
  // for (int i = 0; i < dataSize; i++) {
  //     std::cout << DSS_SA[i] << ", ";
  // }
  // std::cout << std::endl;


  // std::cout << "\nSummary" << std::endl;
  // for (int i : offsets) {
  //     std::cout << i << " ";
  // }
  // std::cout << std::endl;
}

void generateTemplate_LCP(const unsigned char* data, int dataSize, int chunkSize, int modSize) {
  std::vector<std::pair<int, int>> modifiedByteRanges;
  modifiedByteRanges.reserve(dataSize/chunkSize);

  std::vector<int> modifiedByteOffsets;

  std::vector<int> chunkTipOffsets;
  chunkTipOffsets.reserve(dataSize/chunkSize);

  int* buckets = new int[256]();
  int* heads = new int[256]();
  int* tails = new int[256]();
  int* headsIdx = new int[256]();
  int* tailsIdx = new int[256]();

  int (*buckets_d)[256] = new int[256][256]();
  int (*heads_d)[256] = new int[256][256]();
  int (*tails_d)[256] = new int[256][256]();
  int (*headsIdx_d)[256] = new int[256][256]();
  int (*tailsIdx_d)[256] = new int[256][256]();

  std::set<unsigned char> LCMbuckets;
  std::set<unsigned char>* LCMbucketCombos = new std::set<unsigned char>[256];
  std::set<int> offsetGuide;

  unsigned char* firstChunk = new unsigned char[chunkSize];
  unsigned char* finalChunk = new unsigned char[chunkSize];
  unsigned char* runningChunk = new unsigned char[chunkSize];


  int* SA = new int[dataSize + 1];
  std::fill_n(SA, dataSize + 1, -1);
  int* induceDepth = new int[dataSize + 1];
  std::fill_n(induceDepth, dataSize + 1, -1);
  int LMS[dataSize+1];
  std::fill_n(LMS, dataSize+1, -1);
  int lmsOffsets[dataSize+1];
  std::fill_n(lmsOffsets, dataSize+1, -1);

  int LCMlen[dataSize+1];
  std::fill_n(LCMlen, dataSize+1, -1);

  int maxOffset = 0;
  // std::vector<int> LCMledger;

  // std::vector<int> T;
  // std::vector<int> offsets;
  // std::vector<int> chunkLMS;

  unsigned char *lcmsuf=(unsigned char *)malloc((dataSize+1)/8+1); // LS-type array in bits, per-chunk
  memset(lcmsuf, 0, (dataSize+1)/8+1);

  unsigned char *t_global=(unsigned char *)malloc((dataSize+1)/8+1); // LS-type array in bits, per-chunk
  memset(t_global, 0, (dataSize+1)/8+1);

  unsigned char *tloc=(unsigned char *)malloc((dataSize+1)/8+1); // LS-type array in bits, per-chunk
  memset(tloc, 0, (dataSize+1)/8+1);

  unsigned char *lms_global=(unsigned char *)malloc((dataSize+1)/8+1); // LS-type array in bits, globally
  memset(lms_global, 0, (dataSize+1)/8+1);

  int numChunks = dataSize / chunkSize;
  modifiedByteRanges.push_back(std::make_pair(-1, -1));
  chunkTipOffsets.push_back(0);

  for (int chunk = 1; chunk < numChunks; chunk++) {
    const unsigned char* prevChunk = data + (chunk - 1) * chunkSize;
    const unsigned char* currChunk = data + chunk * chunkSize;

    int pos1 = -1;
    int pos2 = -1;

    for (int i = 0; i < chunkSize-1; i++) {
        if (currChunk[i] != prevChunk[i]) {
            if (pos1 == -1) {
                pos1 = i;
            }
            if (pos1 != -1 && i <= pos1+modSize) pos2 = i;
        }
    }

    if (pos1 != -1) {
        modifiedByteRanges.push_back(std::make_pair(pos1, pos2));

        for (int i = pos1; i <= pos2; i++) {
            int offset = currChunk[i] - prevChunk[i];
            modifiedByteOffsets.push_back(offset);
        }
    } else {
        modifiedByteRanges.push_back(std::make_pair(-1, -1));
    }


    int tipOffset = currChunk[chunkSize-1] - prevChunk[chunkSize-1];
    chunkTipOffsets.push_back(tipOffset);
  }

  // Print the template data
  std::cout << "Modified Byte Ranges:" << std::endl;
  for (const auto& range : modifiedByteRanges) {
      std::cout << "[" << range.first << ", " << range.second << "]" << std::endl;
  }

  // for (int i = 0; i < dataSize; i++) {
  //   buckets[data[i]]++;
  //   if (i < dataSize-1) {
  //     buckets_d[data[i]][data[i+1]]++;
  //   } else {
  //     buckets_d[data[i]][0]++;
  //   }
  // }

  for (int i = dataSize-1; i >= 0; i--) {
    buckets[data[i]]++;
    if (i < dataSize-1) {
      tset_global(i, (data[i] < data[i + 1] || (data[i] == data[i + 1] && tget_global(i + 1) == 1)) ? 1 : 0);
      buckets_d[data[i]][data[i+1]]++;
      if (i-PREFETCH_DISTANCE >= 0) {
        __builtin_prefetch(&data[i-PREFETCH_DISTANCE], 0, 3);
      }
    } else {
      buckets_d[data[i]][0]++;
    }
  }

  auto start = std::chrono::steady_clock::now();

  int s = 1; // Leave room for terminator at start
  int s2 = 1; // Leave room for terminator at start
  for (int i = 0; i < 256; i++) {
    if (buckets[i] == 0) continue;
    heads[i] = s;
    headsIdx[i] = s;
    tails[i] = s + buckets[i]-1;
    tailsIdx[i] = s + buckets[i]-1;
    s += buckets[i];
    for (int j = 0; j < 256; j++) {
      if (buckets_d[i][j] == 0) continue;
      heads_d[i][j] = s2;
      headsIdx_d[i][j] = s2;
      tails_d[i][j] = s2 + buckets_d[i][j]-1;
      tailsIdx_d[i][j] = s2 + buckets_d[i][j]-1;
      s2 += buckets_d[i][j];
      if (j+PREFETCH_DISTANCE < 256) {
        __builtin_prefetch(&heads_d[i][j+PREFETCH_DISTANCE], 0, 3);
        __builtin_prefetch(&headsIdx_d[i][j+PREFETCH_DISTANCE], 0, 3);
        __builtin_prefetch(&tails_d[i][j+PREFETCH_DISTANCE], 0, 3);
        __builtin_prefetch(&tailsIdx_d[i][j+PREFETCH_DISTANCE], 0, 3);
      }
    }
  }

  tset_global(dataSize-1, 0); tset_global(dataSize, 1); // the sentinel must be in s1, important!!!
  
  int minLastFirst = -1;
  int maxLastSecond = -1;
  for (int i = numChunks; i-- > 0;) {
    int firstIdx = i*chunkSize;
    if (i < numChunks-1 && modifiedByteRanges[i].second+1 < chunkSize-1 && chunkTipOffsets[i] != -1) {
      lcmset(firstIdx+chunkSize-1, 1);
      SA[tailsIdx_d[data[firstIdx+chunkSize-1]][data[firstIdx+chunkSize]]] = firstIdx+chunkSize-1;
      tailsIdx_d[data[firstIdx+chunkSize-1]][data[firstIdx+chunkSize]]--;
      // LCMbuckets.insert(data[firstIdx+chunkSize-1]);
      // LCMbucketCombos[data[firstIdx+chunkSize-1]].insert(data[firstIdx+chunkSize]);
      lset_global(firstIdx+chunkSize-1, 1);
    }
    if (modifiedByteRanges[i].first != -1) {
      if (maxLastSecond != -1 && maxLastSecond > modifiedByteRanges[i].second) {
        lcmset(firstIdx+maxLastSecond, 1);
        SA[tailsIdx_d[data[firstIdx+maxLastSecond]][data[firstIdx+maxLastSecond+1]]] = firstIdx+maxLastSecond;
        tailsIdx_d[data[firstIdx+maxLastSecond]][data[firstIdx+maxLastSecond+1]]--;
        // LCMbuckets.insert(data[firstIdx+maxLastSecond]);
        // LCMbucketCombos[data[firstIdx+maxLastSecond]].insert(data[firstIdx+maxLastSecond+1]);
        lset_global(firstIdx+maxLastSecond, 1);
      } else {
        maxLastSecond = modifiedByteRanges[i].second;
      }

      for (int j = modifiedByteRanges[i].second; j > modifiedByteRanges[i].first; j--) {
        int suf = j;
        lcmset(firstIdx+suf, 1);
        SA[tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]] = firstIdx+suf;
        tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]--;
        // LCMbuckets.insert(data[firstIdx+suf]);
        // LCMbucketCombos[data[firstIdx+suf]].insert(data[firstIdx+suf+1]);
        lset_global(firstIdx+suf, 1);
      }

      int suf = modifiedByteRanges[i].first;
      lcmset(firstIdx+suf, 1);
      SA[tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]] = firstIdx+suf;
      tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]--;
      // LCMbuckets.insert(data[firstIdx+suf]);
      // LCMbucketCombos[data[firstIdx+suf]].insert(data[firstIdx+suf+1]);
      lset_global(firstIdx+suf, 1);

      if (minLastFirst != -1 && minLastFirst < modifiedByteRanges[i].first) {
        lcmset(firstIdx+minLastFirst, 1);
        SA[tailsIdx_d[data[firstIdx+minLastFirst]][data[firstIdx+minLastFirst+1]]] = firstIdx+minLastFirst;
        tailsIdx_d[data[firstIdx+minLastFirst]][data[firstIdx+minLastFirst+1]]--;
        // LCMbuckets.insert(data[firstIdx+minLastFirst]);
        // LCMbucketCombos[data[firstIdx+minLastFirst]].insert(data[firstIdx+minLastFirst+1]);
        lset_global(firstIdx+minLastFirst, 1);
      } else {
        minLastFirst = modifiedByteRanges[i].first;
      }
    }
  }

  // All LCM suffix double buckets must be fully populated with non-LCM dupes for accuracy
  // This will enable the true detection of positionally relevant suffixes
  for (int i = dataSize; i --> 0;) {
    // 2-byte combos occuring only once provide free relative context
    __builtin_prefetch(&data[i-PREFETCH_DISTANCE], 0, 3);
    if (!lcmget(i) && tget_global(i) && !tget_global(i-1) &&  buckets_d[data[i]][data[i+1]] == 1) {
      lcmset(i, 1);
      SA[tailsIdx_d[data[i]][data[i+1]]] = i;
      tailsIdx_d[data[i]][data[i+1]]--;
      LCMbuckets.insert(data[i]);
      LCMbucketCombos[data[i]].insert(data[i+1]);
      lset_global(i, 1);
    }
    if (!lcmget(i)
      && tailsIdx_d[data[i]][data[i+1]] != tails_d[data[i]][data[i+1]]
    ) {
      lcmset(i, 1);
      SA[tailsIdx_d[data[i]][data[i+1]]] = i;
      tailsIdx_d[data[i]][data[i+1]]--;
      lset_global(i, 1);
    }
  }

  // lcmset(dataSize-1, 1);
  // SA[tailsIdx_d[data[dataSize-1]][0]] = dataSize-1;
  // tailsIdx_d[data[dataSize-1]][0]--;
  // LCMbucketCombos[data[dataSize-1]].insert(0);
  // lset_global(dataSize-1, 1);

  // SA[0] = dataSize;
  // lset_global(dataSize, 1);

  // int keys = 0;
  // int pairs = 0;
  // int trios = 0;
  // for (int i = 0; i < 256; i++) {
  //   for (int j = 0; j < 256; j++) {
  //     if (buckets_d[i][j] == 1) {
  //       // printf("Bucket combo %02X %02X is a key combo\n", i, j);
  //       keys++;
  //     } else if (buckets_d[i][j] == 2) {
  //       // printf("Bucket combo %02X %02X is a key combo\n", i, j);
  //       pairs++;
  //     } else if (buckets_d[i][j] == 3) {
  //       // printf("Bucket combo %02X %02X is a key combo\n", i, j);
  //       trios++;
  //     }
  //   }
  // }

  // printf("%d out of %d suffixes are key suffixes (guaranteed placement first try)\n", keys, dataSize);
  // printf("%d out of %d suffixes are paired suffixes (guaranteed placement with 1 comparison)\n", pairs, dataSize);
  // printf("%d out of %d suffixes are triplet suffixes (guaranteed placement within 2 comparisons)\n", trios, dataSize);


  // int lOffset = 0;
  // int lPos = dataSize;
  // for(int i=dataSize-1; i>=0; i--) {
  //   if (tget_global(i) && !tget_global(i-1)) {
  //     lmsOffsets[lPos] = lOffset;
  //     lPos = i;
  //     maxOffset = std::max(maxOffset, lOffset);
  //     offsetGuide.insert(lOffset);
  //     lOffset = 0;
  //   }
  //   lOffset++;
  // }

  for (int i = 0; i < 256; i++) {
    for (int j = 0; j < 256; j++) {
      __builtin_prefetch(&data[SA[tailsIdx_d[i][j]+1]], 0, 3);
      if (tails_d[i][j] - tailsIdx_d[i][j] > 1) {
        std::sort(&SA[tailsIdx_d[i][j]+1], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
          return sA == dataSize || memcmp(&data[sA+2], &data[sB+2], dataSize) < 0;
        });
      }
    }
  }


  // I need to reorder the chunk progression based on their relative order at d distance from their origins...
  // Precomputed table for each d value maybe? (DISPROVEN, too slow)

  for (int d = 1; d < dataSize; d++) {
    if (tget_local(dataSize)) goto after;
    if (d > 0 && lcmget(dataSize-d)) {tset_local(dataSize, 1); goto after;}
    lset_global(dataSize-d, 1);
    if (d == 1) {
      SA[headsIdx_d[data[dataSize-d]][0]] = dataSize-d;
      headsIdx_d[data[dataSize-d]][0]++;
    } else {
      SA[headsIdx_d[data[dataSize-d]][data[dataSize-d+1]]] = dataSize-d;
      headsIdx_d[data[dataSize-d]][data[dataSize-d+1]]++;
    }
  }

  after:

  for (int i = 0; i < 256; i++) {
    for (int j = 0; j < 256; j++) {
      for (int d = 1; d < dataSize; d++) {
        bool found = false;

        // std::stable_sort(&SA[tailsIdx_d[i][j]+1], &SA[tails_d[i][j]+1], [&](int sA, int sB){
        //   return data[sA-d] < data[sB-d];
        // });

        for (int k = tailsIdx_d[i][j]+1; k < tails_d[i][j]+1; k++) {
          if (tget_local(SA[k]) || SA[k]-d < 1) continue;
          if (d > 0 && lcmget(SA[k]-d)) {tset_local(SA[k], 1); continue;}
          found = true;
          lset_global(SA[k]-d, 1);
          if (d == 1) {
            SA[headsIdx_d[data[SA[k]-d]][i]] = SA[k]-d;
            headsIdx_d[data[SA[k]-d]][i]++;
          } else {
            SA[headsIdx_d[data[SA[k]-d]][data[SA[k]-d+1]]] = SA[k]-d;
            headsIdx_d[data[SA[k]-d]][data[SA[k]-d+1]]++;
          }
        }
        if (!found) break;
      }
      // std::stable_sort(&SA[tailsIdx_d[i][j]+1], &SA[tails_d[i][j]+1], [&](int sA, int sB){
      //   return sA == dataSize || memcmp(&data[sA+2], &data[sB+2], dataSize) < 0;
      // });
    }
  }

  // MARKER

  bool ready = false;

  static double redu_ratio=0;
  static long sum_n=0, sum_n1=0;

  // fprintf(stderr, "\nReduction ratio: %.2lf\n", (double)n1/(dataSize+1));
  // redu_ratio += (double)n1/(dataSize+1);
  // sum_n1+=n1; sum_n+=(dataSize+1);
  // if (name < n1) {
  //   // printf("name: %d\n", name);
  //   SA_IS((unsigned char*)s1, SA1, n1, name-1, sizeof(int), 1);
  // } else {
  //   ready = true;
  //   // printf("level 0, n1 = %d\n", n1);
  //   for(int i=0; i<n1; i++) SA1[s1[i]] = i;
  //   // std::cerr << std::endl << "Recusion ends";
  //   // fprintf(stderr, "\nMean reduction ratio over iterations: %.2lf", redu_ratio);
  //   // fprintf(stderr, "\nMean reduction ratio over characters: %.2lf", (double)sum_n1/sum_n);
  // }
  // printf("\n");

  // std::copy(heads, heads+256, headsIdx); // Reset the back-of-bucket indexes to their original values
  // std::copy(tails, tails+256, tailsIdx); // Reset the back-of-bucket indexes to their original values

  // getBuckets(s, bkt, n, K, cs, true); // find ends of buckets
  // j=0;
  // for(i=1; i<n; i++)
  //   if(isLMS(i)) s1[j++]=i; // get p1
  // for(i=0; i<n1; i++) SA1[i]=s1[SA1[i]]; // get index in s1
  // for(i=n1; i<n; i++) SA[i]=EMPTY; // init SA[n1..n-1]
  // for(i=n1-1; i>=0; i--) {
	//   j=SA[i]; SA[i]=EMPTY;
	//   if(level==0 && i==0)
  //         SA[0]=n-1;
  //     else
  //         SA[bkt[chr(j)]--]=j;
  // }

  // int j = 0;
  // for (int i = 1; i < dataSize+1; i++) {
  //   if (i>0 && tget_global(i) && !tget_global(i-1)) s1[j++]=i;
  // }

  // for (int i = 0; i < n1; i++) SA1[i]=s1[SA1[i]];
  // std::fill_n(SA+n1, dataSize+1-n1, -1);

  // // std::cout << "Before re-adding" << std::endl;
  // // for (int i = 0; i < dataSize+1; i++) {
  // //     std::cout << SA1[i] << ", ";
  // // }
  // // printf("\n");

  // for (int i = n1-1; i >= 0; i--) {
  //   j = SA[i]; SA[i] = -1;
	//   if(i==0)
  //         SA[0]=dataSize;
  //     else {
  //         SA[tailsIdx[data[j]]]=j;
  //         tailsIdx[data[j]]--;
  //     }
  // }


  // // Induce L-type suffixes
  // for (int i = 0; i < dataSize+1; i++){
  //   if (SA[i] <= 0) continue;
  //   j = SA[i]-1;
  //   if (!tget_global(j)) {
  //     SA[headsIdx[data[j]]] = j;
  //     headsIdx[data[j]]++;
  //   }
  // }

  // // std::cout << "After L-R L-inducing" << std::endl;
  // // for (int i = 0; i < dataSize+1; i++) {
  // //     std::cout << SA[i] << ", ";
  // // }
  // // std::cout << std::endl;
  // // printf("\n");

  // // Induce S-type suffixes
  // std::copy(tails, tails+256, tailsIdx); // Reset the back-of-bucket indexes to their original values
  // for (int i = dataSize+1; i -- > 0;){
  //   if (SA[i] <= 0) continue;
  //   j = SA[i]-1;
  //   if (tget_global(j)) {
  //     SA[tailsIdx[data[j]]] = j;
  //     tailsIdx[data[j]]--;
  //   } 
  // }

  auto end = std::chrono::steady_clock::now();
  auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  int compares[] = {2700, 2698};

  // printf("LMS Compare\n");
  // int prevBucket = -1;
  // int lastComp = NULL;
  // for (int s = 0; s < 2; s++) {
  //   if (data[compares[s]] != prevBucket) {printf("\nBucket 0x%02X\n", data[compares[s]]); prevBucket = data[compares[s]]; lastComp = NULL;}
  //   printf("Suffix: %d\n", compares[s]);
  //   for (int i = 0; i < 5; i++) {
  //     printf("%02X ", data[compares[s]+i]);
  //     if (i > 0 && (compares[s] == dataSize-1)) {
  //       if (lastComp == NULL) {
  //         break;
  //       }
  //     } else {
  //       if (lastComp != NULL && data[compares[s]+i] != data[lastComp+i]) {
  //         break;
  //       }
  //     }
  //   }
  //   lastComp = compares[s];
  //   printf("\n");
  // }
  // printf("\n");

  // printf("LCM Readout\n");
  // int prevBucket = -1;
  // int lastComp = NULL;
  // for (int s = 0; s < dataSize+1; s++) {
  //   if (SA[s] == -1 || !lcmget(SA[s])) continue;
  //   if (data[SA[s]] != prevBucket) {printf("\nBucket 0x%02X\n", data[SA[s]]); prevBucket = data[SA[s]]; lastComp = NULL;}
  //   printf("Suffix: %d\n", SA[s]);
  //   for (int i = 0; i < dataSize; i++) {
  //     printf("%02X ", data[SA[s]+i]);
  //     if (i > 0 && (SA[s] == dataSize-1 || lcmget(SA[s]+i))) {
  //       if (lastComp == NULL) {
  //         break;
  //       }
  //     } else {
  //       if (lastComp != NULL && data[SA[s]+i] != data[lastComp+i]) {
  //         break;
  //       }
  //     }
  //   }
  //   lastComp = SA[s];
  //   printf("\n");
  // }
  // printf("\n");

  printf("My Suffix Array took %.6f seconds\n", (double)time.count()/1000000000.0);

  // std::cout << "\nModified Byte Offsets:" << std::endl;
  // for (int offset : modifiedByteOffsets) {
  //     std::cout << offset << " ";
  // }
  // std::cout << std::endl;

  // std::cout << "\nChunk Tip Offsets:" << std::endl;
  // for (int offset : chunkTipOffsets) {
  //     std::cout << offset << " ";
  // }
  // std::cout << std::endl;
  
  // int c;
  // for (int i = dataSize+1; i -- > dataSize - chunkSize;) {
  //   finalChunk[i%chunkSize] = data[i];
  //   c = cmp(data[i], data[i+1]);
  //   if (i < dataSize-1) tset(i%chunkSize, c < 0 ? true : c == 0 ? tget(i%chunkSize+1) : 0); 
    
  //   if (i < dataSize-1 && !tget(i%chunkSize) && tget(i%chunkSize+1)) {
  //     chunkLMS.push_back(i%chunkSize+1);
  //     lset(i%chunkSize+1, 1);
  //     // isLMS_global[i%chunkSize+1] = true;
  //   }
  // }

  // std::cout << "\nFinal chunk suffix types" << std::endl;
  // for (int i = 0; i < chunkSize; i++) {
  //     std::cout << (tget(i) ? "S " : "L ");
  // }
  // std::cout << std::endl;

  // std::cout << "\nFinal chunk LMS suffixes" << std::endl;
  // for (int suf : chunkLMS) {
  //     std::cout << suf << " ";
  // }
  // std::cout << std::endl;

  // not yet implemented, infer the LMS suffixes when placing them in their buckets from right-to-left
  // inference takes advantage of the patterns in the input data

  // std::cout << "Induce Depth" << std::endl;
  // for (int i = 1; i < dataSize+1; i++) {
  //     std::cout << induceDepth[SA[i]] << ", ";
  // }
  // std::cout << std::endl;
  // printf("\n");

  // std::cout << "missing LMS suffixes" << std::endl;
  // for (int i = 1; i < dataSize+1; i++) {
  //   if (tget_global(i) && !tget_global(i-1) && !lget_global(i)) {
  //   // if (lcmget(SA[i])) {
  //     std::cout << i << ", ";
  //   }
  // }
  // std::cout << std::endl;
  // printf("\n");

  // std::cout << "my LMS" << std::endl;
  // for (int i = 1; i < dataSize+1; i++) {
  //   // if (tget_global(SA[i]) && !tget_global(SA[i]-1)) {
  //   // if (lcmget(SA[i])) {
  //     std::cout << SA[i] << ", ";
  //   // }
  // }
  // std::cout << std::endl;
  // printf("\n");

  // int DSS_SA[dataSize];
  // int bA[256];
  // int bB[256*256];
  // divsufsort(data, DSS_SA, dataSize, bA, bB);

  // std::cout << "\nValidated LMS order" << std::endl;
  // for (int i = 0; i < dataSize; i++) {
  //   // if (tget_global(DSS_SA[i]) && !tget_global(DSS_SA[i]-1)) {
  //     std::cout << DSS_SA[i] << ", ";
  //   // } 
  //   // else {
  //   //   std::cout << "-1" << ", ";
  //   // }
  // }
  // std::cout << std::endl;
}

void genData(unsigned char *dest, int len, int chunkSize, int maxMod) {
  std::random_device rd;  // a seed source for the random number engine
  std::mt19937 gen(rd()); // mersenne_twister_engine seeded with rd()
  std::uniform_int_distribution<> p1Rand(0, chunkSize-1);
  std::uniform_int_distribution<> p2Rand(0, maxMod);
  std::uniform_int_distribution<> runRand(1, 11);
  std::uniform_int_distribution<> byteRand(0, 255);
  int i;
  unsigned char buf[chunkSize];
  for (i = 0; i < chunkSize; i++) {
    buf[i] = byteRand(gen);
  }
  int p1 = p1Rand(gen);
  int p2 = p1 + p2Rand(gen);
  int runLength = runRand(gen);
  int c = 0;
  for (int i = 0; i < len/chunkSize; i++) {
    srand(buf[chunkSize-1]);
    c++;
    if (i > 0) {
      if (c == runLength) {
        p1 = p1Rand(gen);
        p2 = p1 + p2Rand(gen);
        p2 = std::min(chunkSize-2, p2);
        runLength = runRand(gen);
        c = 0;
      }

      for (int j = p1; j < p2; j++) {
        buf[j] = rand() % 256;
      }
      buf[chunkSize-1] = rand() % 256;
    }
    memcpy(&dest[i*chunkSize], buf, chunkSize);
  }
}

// Main function
int main() {
  // Dataset 1

  std::ifstream ifs("sample.bin", std::ios::binary);
  ifs.seekg(0, ifs.end);
  size_t size = ifs.tellg();
  unsigned char buffer[size];
  ifs.seekg(0, ifs.beg);
  ifs.read(reinterpret_cast<char*>(buffer), size);
  ifs.close();

  std::cout << "Template for Dataset 1:" << std::endl;
  generateTemplate_LCP(buffer, size, 256, 32);


  int DSS_SA[size];
  int bA[256];
  int bB[256*256];
  auto start = std::chrono::steady_clock::now();
  divsufsort(buffer, DSS_SA, size, bA, bB);
  auto end = std::chrono::steady_clock::now();
  auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  printf("divsufsort took %.6f seconds\n", (double)time.count()/1000000000.0);

  unsigned char s[size+1];
  memcpy(s, buffer, size);
  s[size] = 0;
  int SA[size+1];
  start = std::chrono::steady_clock::now();
  SA_IS(s, SA, (size)+1, 256, sizeof(char), 0);
  end = std::chrono::steady_clock::now();

  time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  printf("SAIS took %.6f seconds\n", (double)time.count()/1000000000.0);

  start = std::chrono::steady_clock::now();
  libsais(s, SA, size, 0, NULL);
  end = std::chrono::steady_clock::now();

  time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  printf("libsais took %.6f seconds\n", (double)time.count()/1000000000.0);

  // int dataSize1 = sizeof(data1);
  // int chunkSize1 = 32;

  // int size = 1536;
  // unsigned char data[size+1];
  // int chunkSize = 32;
  // int maxMod = 4;

  // genData(data, size, chunkSize, maxMod);

  // std::cout << "Template for Dataset 1:" << std::endl;
  // // generateTemplate_SAIS(data, size, chunkSize, maxMod);

  // generateTemplate_LCP(data, size, chunkSize, maxMod);


  // int DSS_SA[size];
  // int bA[256];
  // int bB[256*256];
  // auto start = std::chrono::steady_clock::now();
  // divsufsort(data, DSS_SA, size, bA, bB);
  // auto end = std::chrono::steady_clock::now();
  // auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  // printf("divsufsort took %.6f seconds\n", (double)time.count()/1000000000.0);

  // unsigned char s[size+1];
  // memcpy(s, data, size);
  // s[size] = 0;
  // int SA[size+1];
  // start = std::chrono::steady_clock::now();
  // SA_IS(s, SA, size+1, 256, sizeof(char), 0);
  // end = std::chrono::steady_clock::now();
  // time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  // printf("SAIS took %.6f seconds\n", (double)time.count()/1000000000.0);

  // int dataSize2 = sizeof(data2);
  // int chunkSize2 = 32;

  // std::cout << "Template for Dataset 2:" << std::endl;
  // generateTemplate(data2, dataSize2, chunkSize2, 4);

  // int dataSize3 = sizeof(data2);
  // int chunkSize3 = 32;

  // std::cout << "Template for Dataset 2:" << std::endl;
  // generateTemplate(data3, dataSize3, chunkSize3, 4);

  return 0;
}