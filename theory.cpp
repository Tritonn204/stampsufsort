#include "theory.h"
#include <iostream>
#include <algorithm>
#include <unordered_map>
#include "divsufsort.h"
#include "sais.h"
#include <filesystem>
#include <fstream>
#include <set>

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
#define tget(i) ( (t[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define tset(i, b) t[(i)/8]=(b) ? (mask[(i)%8]|t[(i)/8]) : ((~mask[(i)%8])&t[(i)/8])

#define tget_global(i) ( (t_global[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define tset_global(i, b) t_global[(i)/8]=(b) ? (mask[(i)%8]|t_global[(i)/8]) : ((~mask[(i)%8])&t_global[(i)/8])

#define lget(i) ( (lms[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define lset(i, b) lms[(i)/8]=(b) ? (mask[(i)%8]|lms[(i)/8]) : ((~mask[(i)%8])&lms[(i)/8])

#define lget_global(i) ( (lms_global[(i)/8]&mask[(i)%8]) ? 1 : 0 )
#define lset_global(i, b) lms_global[(i)/8]=(b) ? (mask[(i)%8]|lms_global[(i)/8]) : ((~mask[(i)%8])&lms_global[(i)/8])

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

  unsigned char firstChunk[chunkSize];
  unsigned char finalChunk[chunkSize];
  unsigned char runningChunk[chunkSize];


  int SA[dataSize+1];
  std::fill_n(SA, dataSize+1, -1);
  int N[dataSize+1];
  std::fill_n(N, dataSize+1, -1);

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
  unsigned char *t=(unsigned char *)malloc((chunkSize+1)/8+1); // LS-type array in bits, per-chunk
  unsigned char *t_global=(unsigned char *)malloc((dataSize+1)/8+1); // LS-type array in bits, globally

  memset(lms, 0, (chunkSize+1)/8+1);
  memset(t, 0, (chunkSize+1)/8+1);
  memset(lms_global, 0, (dataSize+1)/8+1);
  memset(t_global, 0, (dataSize+1)/8+1);

  tset_global(dataSize-1, 0);
  tset_global(dataSize, 1);

  std::vector<int> chunkLMS;

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

  int s = 1; // Leave room for terminator at start
  for (int i = 0; i < 256; i++) {
    heads[i] = s;
    headsIdx[i] = s;
    tails[i] = s + buckets[i]-1;
    tailsIdx[i] = s + buckets[i]-1;
    s += buckets[i];
  }

  // Print the template data
  std::cout << "Modified Byte Ranges:" << std::endl;
  for (const auto& range : modifiedByteRanges) {
      std::cout << "[" << range.first << ", " << range.second << "]" << std::endl;
  }

  // std::cout << "\nModified Byte Offsets:" << std::endl;
  // for (int offset : modifiedByteOffsets) {
  //     std::cout << offset << " ";
  // }
  // std::cout << std::endl;

  std::cout << "\nChunk Tip Offsets:" << std::endl;
  for (int offset : chunkTipOffsets) {
      std::cout << offset << " ";
  }
  std::cout << std::endl;

  tset(chunkSize-1, 0);
  lset(chunkSize-1, false);
  tset(chunkSize, 1);
  lset(chunkSize, true);
  
  int c;
  for (int i = dataSize+1; i -- > dataSize - chunkSize;) {
    finalChunk[i%chunkSize] = data[i];
    c = cmp(data[i], data[i+1]);
    if (i < dataSize-1) tset(i%chunkSize, c < 0 ? true : c == 0 ? tget(i%chunkSize+1) : 0); 
    
    if (i < dataSize-1 && !tget(i%chunkSize) && tget(i%chunkSize+1)) {
      chunkLMS.push_back(i%chunkSize+1);
      lset(i%chunkSize+1, 1);
      // isLMS_global[i%chunkSize+1] = true;
    }
  }

  std::cout << "\nFinal chunk suffix types" << std::endl;
  for (int i = 0; i < chunkSize; i++) {
      std::cout << (tget(i) ? "S " : "L ");
  }
  std::cout << std::endl;

  std::cout << "\nFinal chunk LMS suffixes" << std::endl;
  for (int suf : chunkLMS) {
      std::cout << suf << " ";
  }
  std::cout << std::endl;

  // not yet implemented, infer the LMS suffixes when placing them in their buckets from right-to-left
  // inference takes advantage of the patterns in the input data

  std::copy(finalChunk, finalChunk+chunkSize, runningChunk);
  int offIdx = modifiedByteOffsets.size()-1;
  unsigned char nextUp = 0;
  bool nextType = false;

  printf("numchunks: %d\n", numChunks);
  printf("data 46: 0x%02X\n", data[46]);

  LMSledger.push_back(dataSize);
  
  int lastLMS = -1;
  for (int i = numChunks+1; i -- > 1;) {
    int firstIdx = (i-1)*chunkSize;
    std::fill_n(modMask, chunkSize, false);

    bool rem = false;

    if (i < numChunks) {
      if (modifiedByteRanges[i].first != -1) {
        for (int j = modifiedByteRanges[i].second+2; j -- > modifiedByteRanges[i].first-1;) {
          if (j >= modifiedByteRanges[i].first && j <= modifiedByteRanges[i].second) {
            runningChunk[j] -= modifiedByteOffsets[offIdx];
            offIdx--;
            modMask[j] = true;
          }
          c = cmp(runningChunk[j], runningChunk[j+1]);
          tset(j , c < 0 ? 1 : c == 0 ? tget(j+1) : 0);

          if (!tget(j) && tget(j+1)) {
            if (!lget(j+1)) {
              chunkLMS.push_back(j+1);
              lset(j+1, 1);
              // isLMS[j+1] = true;
            }
          } else if (lget(j+1)) {
            // isLMS[j+1] = false;
            lset(j + 1, false);
            rem = true;
          }
        }
      }
      // Process chunk tip independently
      runningChunk[chunkSize-1] -= chunkTipOffsets[i];
      c = cmp(runningChunk[chunkSize-1], nextUp);
      tset(chunkSize-1, c < 0 ? 1 : c == 0 ? nextType : 0);
      // c = cmp(runningChunk[chunkSize-2], runningChunk[chunkSize-1]);
      // tset(chunkSize-2, c < 0 ? 1 : c == 0 ? tget(chunkSize-1) : 0);
      int propCount = 0;
      for (int j = 2; j < chunkSize; j++) {
        int k = j-1;
        int old = tget(chunkSize-j);
        c = cmp(runningChunk[chunkSize-j], runningChunk[chunkSize-k]);
        tset(chunkSize-j, c < 0 ? 1 : c == 0 ? tget(chunkSize-k) : 0);
        if (tget(chunkSize-j) == old) break;
        propCount++;
      }

      // if (firstIdx+chunkSize-2==30) printf("nextUp: 0x%02X, me: 0x%02X," 
      // " type to the left: %d, \nto the right: %d\n"
      // "my type: %d\n", nextUp, runningChunk[chunkSize-2], tget(chunkSize-3), tget(chunkSize-1), tget(chunkSize-2));

      for (int j = 2; j < chunkSize; j++) {
        bool diff = false;
        int k = j-1;
        if (!tget(chunkSize-j) && tget(chunkSize-k)) {
          if (!lget(chunkSize-k)) {
            diff = true;
            chunkLMS.push_back(chunkSize-k);
            lset(chunkSize-k, 1);
            // isLMS[j+1] = true;
          }
        } else if (lget(chunkSize-k)) {
          diff = true;
          lset(chunkSize-k, 0);
          rem = true;
        }
        if (!diff && j-2 > propCount-1) break;
      }

      if (!lget(chunkSize) && nextType && !tget(chunkSize-1)) {
        // isLMS[chunkSize] = true;
        lset(chunkSize, true);
        chunkLMS.insert(chunkLMS.begin(), 1, chunkSize);
      } else if (lget(chunkSize)) {
        // isLMS[chunkSize] = false;
        lset(chunkSize, 0);
        rem = true;
      }  

      if (rem) {
        auto it = std::remove_if(chunkLMS.begin(), chunkLMS.end(), [&](int idx) {
          return !lget(idx);
        });
        chunkLMS.erase(it, chunkLMS.end());
      }

      std::sort(chunkLMS.rbegin(), chunkLMS.rend());
    } else {
      tset(chunkSize-1, false);
      std::sort(chunkLMS.rbegin(), chunkLMS.rend());

      if (rem) {
        auto it = std::remove_if(chunkLMS.begin(), chunkLMS.end(), [&](int idx) {
          return !lget(idx);
        });
        chunkLMS.erase(it, chunkLMS.end());
      }
    }
    tset(chunkSize, nextType);

    printf("Chunk %d\n", i);
    for (int K = 0; K < chunkSize/16; K++) {
      for (int i = 0; i < 16; i++) {
        printf("0x%02X, ", runningChunk[i+K]);
      }
      printf("\n\n");
    }

    std::cout << "LMS suffixes" << std::endl;
    for (int suf : chunkLMS) {
        std::cout << suf << " ";
    }
    std::cout << std::endl << std::endl;

    std::cout << "Suffix Types" << std::endl;
    for (int i = 0; i < chunkSize; i++) {
        std::cout << (tget(i) ? "S " : "L ");
    }
    std::cout << std::endl;

    unsigned char c0;
    for (int suffix : chunkLMS) {
      c0 = runningChunk[suffix];
      SA[tailsIdx[c0]] = suffix+firstIdx;
      lset_global(suffix+firstIdx, true);
      tailsIdx[c0]--;
      int len = 0;
      if (lastLMS != -1) {
        len = (suffix - lastLMS + 1);
      } else {
        len = dataSize - (suffix + firstIdx) + 1;
      }

      LMSlen[suffix] = len;
      if (suffix > 0) IS_L[suffix] = runningChunk[suffix-1];
      else IS_L[suffix] = data[suffix-1];
      lastLMS = suffix;
    }

    for (int i = 1; i < chunkSize+1; i++) {
      tset_global(i+firstIdx, tget(i));
    }

    lastLMS += chunkSize;
    nextUp = runningChunk[0];
    nextType = tget(0);
  }
  printf("\n");

  for (int i = dataSize; i >= 0; i--) {
    if (lget_global(i)) printf("%d, ", i);
  }


  SA[0] = dataSize;
  lset_global(dataSize, 1);
  tset_global(dataSize, 1);
  lset_global(dataSize-1, 0);
  tset_global(dataSize-1, 0);

  printf("\n");

  std::cout << "After LMS sort" << std::endl;
  for (int i = 0; i < dataSize+1; i++) {
      std::cout << SA[i] << ", ";
  }
  std::cout << std::endl;
  printf("\n");

  // // Induce terminator L suffix
  // SA[headsIdx[data[dataSize-1]]] = dataSize-1;
  // headsIdx[data[dataSize-1]]++;
  // if (!tget_global(dataSize-2)) IS_L[dataSize-1] = data[dataSize-2];
  // else IS_S[dataSize-1] = data[dataSize-2];

  for (int i = 0; i < dataSize+1; i++){
    if (SA[i] <= 0) continue;
    int j = SA[i]-1;
    if (!tget_global(j)) {
      SA[headsIdx[data[j]]] = j;
      headsIdx[data[j]]++;
    }
  }

  std::cout << "After L-R L-inducing" << std::endl;
  for (int i = 0; i < dataSize+1; i++) {
      std::cout << SA[i] << ", ";
  }
  std::cout << std::endl;
  printf("\n");

  // Induce S-type suffixes
  std::copy(tails, tails+256, tailsIdx); // Reset the back-of-bucket indexes to their original values
  for (int i = dataSize+1; i -- > 0;){
    if (SA[i] <= 0) continue;
    int j = SA[i]-1;
    if (tget_global(j)) {
      SA[tailsIdx[data[j]]] = j;
      tailsIdx[data[j]]--;
    } 
  }

  std::cout << "After R-L S-inducing" << std::endl;
  for (int i = 0; i < dataSize+1; i++) {
      std::cout << SA[i] << ", ";
  }
  std::cout << std::endl;
  printf("\n");

  int n1 = 0;
  for (int i = 0; i < dataSize+1; i++) {
    if (lget_global(SA[i])) SA[n1++] = SA[i];
  }

  std::fill_n(SA+n1, dataSize+1-n1, -1);

  std::cout << "After LMS Packing" << std::endl;
  for (int i = 0; i < dataSize+1; i++) {
      std::cout << SA[i] << ", ";
  }
  std::cout << std::endl;


  int i = 0, j = 0;
  int name = 0;
  lastLMS = -1;
  for (i = 0; i < n1; i++) {
    int pos = SA[i]; bool diff = false;
    for(int d=0; d<dataSize+1; d++)
      if(lastLMS==-1 || pos+d==dataSize || lastLMS+d==dataSize ||
          data[pos+d]!=data[lastLMS+d] ||
          tget_global(pos+d)!=tget_global(lastLMS+d))
      { diff=true; break; }
      else
        if(d>0 && (lget_global(pos+d) || lget_global(lastLMS+d)))
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

  std::cout << "\nS1 is ready" << std::endl;
  for (int i = 0; i < dataSize+1; i++) {
      std::cout << SA[i] << ", ";
  }
  std::cout << std::endl;
  printf("\n");

  bool ready = false;

  static double redu_ratio=0;
  static long sum_n=0, sum_n1=0;

  fprintf(stderr, "\nReduction ratio: %.2lf\n", (double)n1/(dataSize+1));
  redu_ratio += (double)n1/(dataSize+1);
  sum_n1+=n1; sum_n+=(dataSize+1);
  if (name < n1) {
    printf("name: %d\n", name);
    SA_IS((unsigned char*)s1, SA1, n1, name, sizeof(int), 1);
  } else {
    ready = true;
    printf("level 0, n1 = %d\n", n1);
    for(i=0; i<n1; i++) SA1[s1[i]] = i;
    std::cerr << std::endl << "Recusion ends";
    fprintf(stderr, "\nMean reduction ratio over iterations: %.2lf", redu_ratio);
    fprintf(stderr, "\nMean reduction ratio over characters: %.2lf", (double)sum_n1/sum_n);
  }
  printf("\n");

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
    if (lget_global(i)) s1[j++]=i;
  }

  for (i = 0; i < n1; i++) SA1[i]=s1[SA1[i]];
  std::fill_n(SA+n1, dataSize+1-n1, -1);

  std::cout << "Before re-adding" << std::endl;
  for (int i = 0; i < dataSize+1; i++) {
      std::cout << SA1[i] << ", ";
  }
  printf("\n");

  for (int i = n1-1; i >= 0; i--) {
    j = SA[i]; SA[i] = -1;
	  if(i==0)
          SA[0]=dataSize;
      else {
          SA[tailsIdx[data[j]]]=j;
          tailsIdx[data[j]]--;
      }
  }


  // Induce L-type suffixes
  for (int i = 0; i < dataSize+1; i++){
    if (SA[i] <= 0) continue;
    int j = SA[i]-1;
    if (!tget_global(j)) {
      SA[headsIdx[data[j]]] = j;
      headsIdx[data[j]]++;
    }
  }

  std::cout << "After L-R L-inducing" << std::endl;
  for (int i = 0; i < dataSize+1; i++) {
      std::cout << SA[i] << ", ";
  }
  std::cout << std::endl;
  printf("\n");

  // Induce S-type suffixes
  std::copy(tails, tails+256, tailsIdx); // Reset the back-of-bucket indexes to their original values
  for (int i = dataSize+1; i -- > 0;){
    if (SA[i] <= 0) continue;
    int j = SA[i]-1;
    if (tget_global(j)) {
      SA[tailsIdx[data[j]]] = j;
      tailsIdx[data[j]]--;
    } 
  }

  std::cout << "Final" << std::endl;
  for (int i = 1; i < dataSize+1; i++) {
      std::cout << SA[i] << ", ";
  }
  std::cout << std::endl;
  printf("\n");

  int DSS_SA[dataSize];
  int bA[256];
  int bB[256*256];
  divsufsort(data, DSS_SA, dataSize, bA, bB);

  std::cout << "\nValidated Suffix Array" << std::endl;
  for (int i = 0; i < dataSize; i++) {
      std::cout << DSS_SA[i] << ", ";
  }
  std::cout << std::endl;


  std::cout << "\nSummary" << std::endl;
  for (int i : offsets) {
      std::cout << i << " ";
  }
  std::cout << std::endl;
}

void generateTemplate_LCP(const unsigned char* data, int dataSize, int chunkSize, int modSize) {
  std::vector<std::pair<int, int>> modifiedByteRanges;
  std::vector<int> modifiedByteOffsets;
  std::vector<int> chunkTipOffsets;
  std::unordered_map<std::string, LMSInfo> lmsMap;

  int buckets[256] = {0};
  int heads[256] = {0};
  int tails[256] = {0};
  int headsIdx[256] = {0};
  int tailsIdx[256] = {0};

  unsigned char firstChunk[chunkSize];
  unsigned char finalChunk[chunkSize];
  unsigned char runningChunk[chunkSize];

  int SA[dataSize+1];
  std::fill_n(SA, dataSize+1, -1);
  int N[dataSize+1];
  std::fill_n(N, dataSize+1, -1);

  int LCMlen[dataSize+1];
  std::fill_n(LCMlen, dataSize+1, -1);
  std::vector<int> LCMledger;

  std::vector<int> T;
  std::vector<int> offsets;
  std::vector<int> chunkLMS;

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

  int s = 1; // Leave room for terminator at start
  for (int i = 0; i < 256; i++) {
    heads[i] = s;
    headsIdx[i] = s;
    tails[i] = s + buckets[i]-1;
    tailsIdx[i] = s + buckets[i]-1;
    s += buckets[i];
  }

  // Print the template data
  std::cout << "Modified Byte Ranges:" << std::endl;
  for (const auto& range : modifiedByteRanges) {
      std::cout << "[" << range.first << ", " << range.second << "]" << std::endl;
  }

  std::cout << "\nModified Byte Offsets:" << std::endl;
  for (int offset : modifiedByteOffsets) {
      std::cout << offset << " ";
  }
  std::cout << std::endl;

  std::cout << "\nChunk Tip Offsets:" << std::endl;
  for (int offset : chunkTipOffsets) {
      std::cout << offset << " ";
  }
  std::cout << std::endl;
  
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

  std::pair<int,int> lastMod(-1,-1);
  std::pair<int,int> *newMod;

  std::set<int> LCMlengths;

  LCMledger.push_back(0);
  LCMlengths.insert(chunkSize-1);
  LCMlen[0] = chunkSize-1;

  for (int i = 1; i < numChunks; i++) {
    int firstIdx = i*chunkSize;
    newMod = &modifiedByteRanges[i];

    if (newMod->first == -1) {
      if (lastMod.first != -1) {
        LCMledger.push_back(firstIdx-1);
        LCMlengths.insert(lastMod.first+2);
        LCMlen[firstIdx-1] = lastMod.first+2;

        if (lastMod.first != 0) {
          LCMledger.push_back(firstIdx);
          LCMlengths.insert(lastMod.first+1);
          LCMlen[firstIdx] = lastMod.first+1;
        }
        
        LCMledger.push_back(firstIdx+lastMod.first);
        LCMlengths.insert(chunkSize-lastMod.first);
        LCMlen[firstIdx+lastMod.first] = chunkSize-lastMod.first;

        if (lastMod.first != lastMod.second) {
          LCMledger.push_back(firstIdx+lastMod.second);
          LCMlengths.insert(chunkSize-lastMod.second);
          LCMlen[firstIdx+lastMod.second] = chunkSize-lastMod.second;
        }

      } else {
        LCMledger.push_back(firstIdx-1);
        LCMlengths.insert(chunkSize);
        LCMlen[firstIdx-1] = chunkSize;

        LCMledger.push_back(firstIdx);
        LCMlengths.insert(chunkSize-1);
        LCMlen[firstIdx] = chunkSize-1;
      }
    } else {
      LCMledger.push_back(firstIdx-1);
      LCMlengths.insert(newMod->first+2);
      LCMlen[firstIdx-1] = newMod->first+2;

      if (newMod->first != 0){
        LCMledger.push_back(firstIdx);
        LCMlengths.insert(newMod->first+1);
        LCMlen[firstIdx] = newMod->first+1;
      }

      LCMledger.push_back(firstIdx+newMod->first);
      LCMlengths.insert(chunkSize-newMod->first);
      LCMlen[firstIdx+newMod->first] = chunkSize-newMod->first;

      if (newMod->first != newMod->second){
        LCMledger.push_back(firstIdx+newMod->second);
        LCMlengths.insert(chunkSize-newMod->second);
        LCMlen[firstIdx+newMod->second] = chunkSize-newMod->second;
      }

      lastMod = *newMod;
    }
  }

  std::vector<std::vector<std::vector<int>>> firstSort;
  std::vector<std::vector<std::vector<std::vector<int>>>> secondSort;
  std::vector<std::vector<std::vector<std::vector<int>>>> thirdSort;

  firstSort.resize(256);
  secondSort.resize(256);
  thirdSort.resize(256);
  for (int i = 0; i < 256; i++) {
    firstSort[i].resize(chunkSize+2);
    secondSort[i].resize(chunkSize+2);
    thirdSort[i].resize(chunkSize+2);
  }

  // printf("LCM Readout\n");
  for (int LCM : LCMledger) {
    int len = LCMlen[LCM];
    firstSort[data[LCM]][len].push_back(LCM);
    // printf("Suffix: %d\n", LCM);
    // for (int i = 0; i < len; i++) {
    //   printf("%02X ", data[LCM+i]);
    // }
    // printf("\n");
  }
  // printf("\n");

  for (int i = 0; i < 256; i++) {
    for (int j : LCMlengths) {
      std::sort(firstSort[i][j].begin(), firstSort[i][j].end(), [&](int sA, int sB) {
        int len = std::min(LCMlen[sA], LCMlen[sB]);
        bool thirdCheck = len > 2;
        return (data[sA+len-1] < data[sB+len-1] && data[sA+1] <= data[sB+1] && (thirdCheck && data[sA+2] <= data[sB+2]));
      });
    }
  }

  printf("LCM First Sort Result\n");
  int i = 0;
  for (std::vector<std::vector<int>> ledger : firstSort) {
    for(int j : LCMlengths) {
      if (ledger[j].size() > 0) printf("Bucket %02X\n", i);
      for (int LCM : ledger[j]) {
        int len = LCMlen[LCM];
        printf("Suffix: %d\n", LCM);
        for (int i = 0; i < len; i++) {
          printf("%02X ", data[LCM+i]);
        }
        printf("\n");
      }
      if (ledger[j].size() > 0) printf("\n");
    }
    i++;
  }


  std::copy(finalChunk, finalChunk+chunkSize, runningChunk);
  int offIdx = modifiedByteOffsets.size()-1;
  unsigned char nextUp = 0;
  bool nextType = false;

  // int lastLMS = -1;
  // for (int i = numChunks+1; i -- > 1;) {
  //   int firstIdx = (i-1)*chunkSize;
  //   std::fill_n(modMask, chunkSize, false);

  //   bool rem = false;

  //   if (i < numChunks) {
  //     if (modifiedByteRanges[i].first != -1) {
  //       for (int j = modifiedByteRanges[i].second+2; j -- > modifiedByteRanges[i].first-1;) {
  //         if (j >= modifiedByteRanges[i].first && j <= modifiedByteRanges[i].second) {
  //           runningChunk[j] -= modifiedByteOffsets[offIdx];
  //           offIdx--;
  //           modMask[j] = true;
  //         }
  //         c = cmp(runningChunk[j], runningChunk[j+1]);
  //         tset(j , c < 0 ? 1 : c == 0 ? tget(j+1) : 0);

  //         if (!tget(j) && tget(j+1)) {
  //           if (!lget(j+1)) {
  //             chunkLMS.push_back(j+1);
  //             lset(j+1, 1);
  //             // isLMS[j+1] = true;
  //           }
  //         } else if (lget(j+1)) {
  //           // isLMS[j+1] = false;
  //           lset(j + 1, false);
  //           rem = true;
  //         }
  //       }
  //     }
  //     // Process chunk tip independently
  //     runningChunk[chunkSize-1] -= chunkTipOffsets[i];
  //     c = cmp(runningChunk[chunkSize-1], nextUp);
  //     tset(chunkSize-1, c < 0 ? 1 : c == 0 ? nextType : 0);
  //     // c = cmp(runningChunk[chunkSize-2], runningChunk[chunkSize-1]);
  //     // tset(chunkSize-2, c < 0 ? 1 : c == 0 ? tget(chunkSize-1) : 0);
  //     int propCount = 0;
  //     for (int j = 2; j < chunkSize; j++) {
  //       int k = j-1;
  //       int old = tget(chunkSize-j);
  //       c = cmp(runningChunk[chunkSize-j], runningChunk[chunkSize-k]);
  //       tset(chunkSize-j, c < 0 ? 1 : c == 0 ? tget(chunkSize-k) : 0);
  //       if (tget(chunkSize-j) == old) break;
  //       propCount++;
  //     }

  //     // if (firstIdx+chunkSize-2==30) printf("nextUp: 0x%02X, me: 0x%02X," 
  //     // " type to the left: %d, \nto the right: %d\n"
  //     // "my type: %d\n", nextUp, runningChunk[chunkSize-2], tget(chunkSize-3), tget(chunkSize-1), tget(chunkSize-2));

  //     for (int j = 2; j < chunkSize; j++) {
  //       bool diff = false;
  //       int k = j-1;
  //       if (!tget(chunkSize-j) && tget(chunkSize-k)) {
  //         if (!lget(chunkSize-k)) {
  //           diff = true;
  //           chunkLMS.push_back(chunkSize-k);
  //           lset(chunkSize-k, 1);
  //           // isLMS[j+1] = true;
  //         }
  //       } else if (lget(chunkSize-k)) {
  //         diff = true;
  //         lset(chunkSize-k, 0);
  //         rem = true;
  //       }
  //       if (!diff && j-2 > propCount-1) break;
  //     }

  //     if (!lget(chunkSize) && nextType && !tget(chunkSize-1)) {
  //       // isLMS[chunkSize] = true;
  //       lset(chunkSize, true);
  //       chunkLMS.insert(chunkLMS.begin(), 1, chunkSize);
  //     } else if (lget(chunkSize)) {
  //       // isLMS[chunkSize] = false;
  //       lset(chunkSize, 0);
  //       rem = true;
  //     }  

  //     if (rem) {
  //       auto it = std::remove_if(chunkLMS.begin(), chunkLMS.end(), [&](int idx) {
  //         return !lget(idx);
  //       });
  //       chunkLMS.erase(it, chunkLMS.end());
  //     }

  //     std::sort(chunkLMS.rbegin(), chunkLMS.rend());
  //   } else {
  //     tset(chunkSize-1, false);
  //     std::sort(chunkLMS.rbegin(), chunkLMS.rend());

  //     if (rem) {
  //       auto it = std::remove_if(chunkLMS.begin(), chunkLMS.end(), [&](int idx) {
  //         return !lget(idx);
  //       });
  //       chunkLMS.erase(it, chunkLMS.end());
  //     }
  //   }
  //   tset(chunkSize, nextType);

  //   printf("Chunk %d\n", i);
  //   for (int K = 0; K < chunkSize/16; K++) {
  //     for (int i = 0; i < 16; i++) {
  //       printf("0x%02X, ", runningChunk[i+K]);
  //     }
  //     printf("\n\n");
  //   }

  //   std::cout << "LMS suffixes" << std::endl;
  //   for (int suf : chunkLMS) {
  //       std::cout << suf << " ";
  //   }
  //   std::cout << std::endl << std::endl;

  //   std::cout << "Suffix Types" << std::endl;
  //   for (int i = 0; i < chunkSize; i++) {
  //       std::cout << (tget(i) ? "S " : "L ");
  //   }
  //   std::cout << std::endl;

  //   unsigned char c0;
  //   for (int suffix : chunkLMS) {
  //     c0 = runningChunk[suffix];
  //     SA[tailsIdx[c0]] = suffix+firstIdx;
  //     lset_global(suffix+firstIdx, true);
  //     tailsIdx[c0]--;
  //     int len = 0;
  //     if (lastLMS != -1) {
  //       len = (suffix - lastLMS + 1);
  //     } else {
  //       len = dataSize - (suffix + firstIdx) + 1;
  //     }

  //     LMSlen[suffix] = len;
  //     if (suffix > 0) IS_L[suffix] = runningChunk[suffix-1];
  //     else IS_L[suffix] = data[suffix-1];
  //     lastLMS = suffix;
  //   }

  //   for (int i = 1; i < chunkSize+1; i++) {
  //     tset_global(i+firstIdx, tget(i));
  //   }

  //   lastLMS += chunkSize;
  //   nextUp = runningChunk[0];
  //   nextType = tget(0);
  // }
}

// Main function
int main() {
    // Dataset 1

  unsigned char *buffer = reinterpret_cast<unsigned char *>(malloc(98559));

  std::ifstream ifs("sample.bin", std::ios::binary);
  ifs.seekg(0, ifs.end);
  size_t size = ifs.tellg(); 
  ifs.seekg(0, ifs.beg);
  ifs.read(reinterpret_cast<char*>(buffer), size);
  ifs.close();

  int dataSize1 = sizeof(data2);
  int chunkSize1 = 32;

  std::cout << "Template for Dataset 1:" << std::endl;
  generateTemplate_LCP(buffer, size, 256, 32);

  // unsigned char s[dataSize1+1];
  // memcpy(s, data4, dataSize1);
  // s[dataSize1] = 0;
  // int SA[dataSize1+1];
  // SA_IS(s, SA, dataSize1+1, 256, sizeof(char), 0);

  // std::cout << "After R-L S-inducing" << std::endl;
  // for (int i = 1; i < dataSize1; i++) {
  //     std::cout << SA[i] << ", ";
  // }

  // std::cout << std::endl;
  

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