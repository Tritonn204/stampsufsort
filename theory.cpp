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
#include <cassert>
#include <immintrin.h>
#include <cstdint>

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

#define NAIVESORT_CONST 9999999

int cmp(unsigned char x, unsigned char y){ 
   return (x==y)?0:(x>y)?1:-1; 
}

// void fastMemcpy(void *pvDest, void *pvSrc, size_t nBytes) {
//   assert(nBytes % 32 == 0);
//   assert((intptr_t(pvDest) & 31) == 0);
//   assert((intptr_t(pvSrc) & 31) == 0);
//   const __m256i *pSrc = reinterpret_cast<const __m256i*>(pvSrc);
//   __m256i *pDest = reinterpret_cast<__m256i*>(pvDest);
//   int64_t nVects = nBytes / sizeof(*pSrc);
//   for (; nVects > 0; nVects--, pSrc++, pDest++) {
//     const __m256i loaded = _mm256_stream_load_si256(pSrc);
//     _mm256_stream_si256(pDest, loaded);
//   }
//   _mm_sfence();
// }

// Function to sort an array using
// insertion sort
template<typename F>
void insertionSufSort32(int arr[], int n, F &&lambda)
{
    int i, key, j;
    for (i = 1; i < n; i++) {
        key = arr[i];
        j = i - 1;

        // Move elements of arr[0..i-1],
        // that are greater than key, 
        // to one position ahead of their
        // current position
        while (j >= 0 && lambda(arr[j], key) > 0) {
            arr[j + 1] = arr[j];
            j = j - 1;
        }
        arr[j + 1] = key;
    }
}

template<typename F>
void insertionSufSort(uint64_t arr[], int n, F &&lambda)
{
    int i, key, j;
    for (i = 1; i < n; i++) {
        key = arr[i];
        j = i - 1;

        // Move elements of arr[0..i-1],
        // that are greater than key, 
        // to one position ahead of their
        // current position
        while (j >= 0 && lambda(arr[j], key) > 0) {
            arr[j + 1] = arr[j];
            j = j - 1;
        }
        arr[j + 1] = key;
    }
}

// void fastMemcpy(void *pvDest, void *pvSrc, size_t nBytes) {
//   const __m256i *pSrc = reinterpret_cast<const __m256i*>(pvSrc);
//   __m256i *pDest = reinterpret_cast<__m256i*>(pvDest);
  
//   // Copy 32-byte vectors
//   size_t nVects = nBytes / sizeof(*pSrc);
//   for (; nVects > 0; nVects--, pSrc++, pDest++) {
//     const __m256i loaded = _mm256_loadu_si256(pSrc);
//     _mm256_storeu_si256(pDest, loaded);
//   }
  
//   // Handle remaining bytes
//   const int *remainingSrc = reinterpret_cast<const int*>(pSrc);
//   int *remainingDest = reinterpret_cast<int*>(pDest);
//   size_t remainingBytes = nBytes % sizeof(*pSrc);
//   size_t remainingInts = remainingBytes / sizeof(int);
  
//   if (remainingInts > 0) {
//     // Create a mask for the remaining integers
//     const int mask[8] = {
//       (remainingInts > 0) ? -1 : 0,
//       (remainingInts > 1) ? -1 : 0,
//       (remainingInts > 2) ? -1 : 0,
//       (remainingInts > 3) ? -1 : 0,
//       (remainingInts > 4) ? -1 : 0,
//       (remainingInts > 5) ? -1 : 0,
//       (remainingInts > 6) ? -1 : 0,
//       (remainingInts > 7) ? -1 : 0
//     };
    
//     const __m256i maskVec = _mm256_loadu_si256(reinterpret_cast<const __m256i*>(mask));
//     const __m256i loaded = _mm256_maskload_epi32(remainingSrc, maskVec);
//     _mm256_maskstore_epi32(remainingDest, maskVec, loaded);
//   }
// }

// Function to get the largest element from an array
int getMax(int array[], int n) {
  int max = array[0];
  for (int i = 1; i < n; i++)
    if (array[i] > max)
      max = array[i];
  return max;
}

// Using counting sort to sort the elements in the basis of significant places
void countingSort(int array[], int size, int place) {
  const int max = 10;
  int output[size];
  int count[max];

  for (int i = 0; i < max; ++i)
    count[i] = 0;

  // Calculate count of elements
  for (int i = 0; i < size; i++)
    count[(array[i] / place) % 10]++;

  // Calculate cumulative count
  for (int i = 1; i < max; i++)
    count[i] += count[i - 1];

  // Place the elements in sorted order
  for (int i = size - 1; i >= 0; i--) {
    output[count[(array[i] / place) % 10] - 1] = array[i];
    count[(array[i] / place) % 10]--;
  }

  for (int i = 0; i < size; i++)
    array[i] = output[i];
}

// Main function to implement radix sort
void radixsort(int array[], int size) {
  // Get maximum element
  int max = getMax(array, size);

  // Apply counting sort to sort elements based on place value.
  for (int place = 1; max / place > 0; place *= 10)
    countingSort(array, size, place);
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

  unsigned char *zeroDist = new unsigned char[dataSize+1]();

  int (*buckets_d)[256] = new int[256][256]();
  int (*heads_d)[256] = new int[256][256]();
  int (*tails_d)[256] = new int[256][256]();
  int (*headsIdx_d)[256] = new int[256][256]();
  int (*tailsIdx_d)[256] = new int[256][256]();
  

  std::vector<std::vector<std::set<int, std::greater<int>>>> prefixLen(256, std::vector<std::set<int, std::greater<int>>>(256));

  std::set<unsigned char> LCMbuckets;
  std::set<unsigned char>* LCMbucketCombos = new std::set<unsigned char>[256];
  std::set<int> offsetGuide;

  unsigned char* firstChunk = new unsigned char[chunkSize];
  unsigned char* finalChunk = new unsigned char[chunkSize];
  unsigned char* runningChunk = new unsigned char[chunkSize];

  int inferenceDist[dataSize+1];
  std::fill_n(inferenceDist, dataSize + 1, 0);
  int compLen[dataSize+1];
  std::fill_n(compLen, dataSize + 1, 0);

  int* SA = new int[dataSize + 1];
  std::fill_n(SA, dataSize + 1, -1);
  uint64_t LCM[dataSize+1];
  std::fill_n(LCM, dataSize+1, -1);
  int* finalSA = new int[dataSize + 1];
  std::fill_n(finalSA, dataSize + 1, -1);
  int* packedBucketHeadIndexes = new int[dataSize + 1];
  std::fill_n(packedBucketHeadIndexes, dataSize + 1, -1);
  unsigned char* packedBucketHeadOffsets = new unsigned char[dataSize + 1];
  std::fill_n(packedBucketHeadOffsets, dataSize + 1, 0);

  int lmsOffsets[dataSize+1];
  std::fill_n(lmsOffsets, dataSize+1, -1);

  int LCMlen[dataSize+1];
  std::fill_n(LCMlen, dataSize+1, -1);
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

  // int numChunks = dataSize / chunkSize;
  int numCompleteChunks = dataSize / chunkSize;
  int finalChunkSize = dataSize % chunkSize;

  modifiedByteRanges.push_back(std::make_pair(-1, -1));
  chunkTipOffsets.push_back(0);

  int inductionData[256][256];
  for (int i = 0; i < 256; i++) {
    for (int j = 0; j < 256; j++) {
      inductionData[i][j] = -1;
    }
  }

  int rootBytes[256][256];
  for (int i = 0; i < 256; i++) {
    for (int j = 0; j < 256; j++) {
      rootBytes[i][j] = -1;
    }
  }

  for (int chunk = 1; chunk < numCompleteChunks+1; chunk++) {
    const unsigned char* prevChunk = data + (chunk - 1) * chunkSize;
    const unsigned char* currChunk = data + chunk * chunkSize;

    int pos1 = -1;
    int pos2 = -1;

    for (int i = 0;  chunk*chunkSize + i < dataSize && i < chunkSize-1; i++) {
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

  printf("Numchunks: %.4f, finalChunkSize: %d\n", dataSize/256.0, finalChunkSize);

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
      if (buckets_d[i][j] == 0) {
        continue;
      }
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
  int lastLCMpos = -1;
  int newLCMlen = 0;

  int prevLCM = dataSize+1;
  // Process the incomplete final chunk
  if (finalChunkSize > 0) {
    int firstIdx = numCompleteChunks * chunkSize;

    if (modifiedByteRanges[numCompleteChunks].first != -1) {
      int suf = modifiedByteRanges[numCompleteChunks].second;
      if (firstIdx + suf < dataSize) {
        lcmset(firstIdx+suf, 1);
        SA[tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]] = firstIdx+suf;
        tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]--;
        // lset_global(firstIdx+suf, 1);
        // newLCMlen = std::max((chunkSize-1) - modifiedByteRanges[numCompleteChunks].second, 1);
        // prefixLen[data[firstIdx+suf]][data[firstIdx+suf+1]].insert(newLCMlen);
        compLen[prevLCM] = prevLCM - (firstIdx+suf) + 2;
        prevLCM = firstIdx+suf;

      //   // Place all newly modified bytes between first & second directly into LCM array
      //   // These will be sorted alongside the rest of the data in the second/reduction sort process
      //   for (int j = modifiedByteRanges[numCompleteChunks].second-1; j > modifiedByteRanges[numCompleteChunks].first-2; j--) {
      //     lcmset(firstIdx+j, 1);
      //     LCM[headsIdx_d[data[firstIdx+j]][data[firstIdx+j+1]]] = firstIdx+j | (1 << 17);
      //     headsIdx_d[data[firstIdx+j]][data[firstIdx+j+1]]++;
      //   }
      }

      suf = modifiedByteRanges[numCompleteChunks].first-2;
      if (firstIdx + suf < dataSize) {
        lcmset(firstIdx+suf, 1);
        SA[tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]] = firstIdx+suf;
        tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]--;
        // lset_global(firstIdx+suf, 1);
        // prefixLen[data[firstIdx+suf]][data[firstIdx+suf+1]].insert(2);
        compLen[prevLCM] = prevLCM - (firstIdx+suf) + 2;
        prevLCM = firstIdx+suf;
      }
    }
  }

  for (int i = numCompleteChunks; i-- > 0;) {
    int firstIdx = i*chunkSize;
    // __builtin_prefetch(&data[firstIdx+modifiedByteRanges[i].first], 0, 3);
    if (i > 0)
      __builtin_prefetch(&data[firstIdx+modifiedByteRanges[i-1].first], 0, 3);

    if (i == numCompleteChunks-1 || (modifiedByteRanges[i].second+1 < chunkSize-1 && chunkTipOffsets[i] != -1)) {
      int suf = chunkSize-3;
      lcmset(firstIdx+suf, 1);
      SA[tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]] = firstIdx+suf;
      tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]--;
      // lset_global(firstIdx+chunkSize-1, 1);
      // if (i == numCompleteChunks-1) {
      //   newLCMlen = std::max(modifiedByteRanges[i+1].first+2, finalChunkSize+2);
      // } else {
      //   newLCMlen = modifiedByteRanges[i+1].first+1;
      // }
      // newLCMlen = prevLCM - (firstIdx+chunkSize-1);
      // prefixLen[data[firstIdx+chunkSize-1]][data[firstIdx+chunkSize]].insert(newLCMlen);
      compLen[prevLCM] = prevLCM - (firstIdx+suf) + 2;
      prevLCM = firstIdx+suf;
    }
    if (modifiedByteRanges[i].first != -1) {
      int suf = modifiedByteRanges[i].second;
      lcmset(firstIdx+suf, 1);
      SA[tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]] = firstIdx+suf;
      tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]--;
      // lset_global(firstIdx+suf, 1);
      // newLCMlen = std::max((chunkSize-1) - modifiedByteRanges[i].second, 1);
      // newLCMlen = prevLCM - (firstIdx + suf);
      // prefixLen[data[firstIdx+suf]][data[firstIdx+suf+1]].insert(newLCMlen);
      compLen[prevLCM] = prevLCM - (firstIdx+suf) + 2;
      prevLCM = firstIdx+suf;

      // // Place all newly modified bytes between first & second directly into LCM array
      // // These will be sorted alongside the rest of the data in the second/reduction sort process
      // for (int j = modifiedByteRanges[numCompleteChunks].second-1; j > modifiedByteRanges[numCompleteChunks].first-2; j--) {
      //   lcmset(firstIdx+j, 1);
      //   LCM[headsIdx_d[data[firstIdx+j]][data[firstIdx+j+1]]] = firstIdx+j | (1 << 17);
      //   headsIdx_d[data[firstIdx+j]][data[firstIdx+j+1]]++;
      // }

      suf = modifiedByteRanges[i].first-2;
      if (true) {
        lcmset(firstIdx+suf, 1);
        SA[tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]] = firstIdx+suf;
        tailsIdx_d[data[firstIdx+suf]][data[firstIdx+suf+1]]--;
        // lset_global(firstIdx+suf, 1);
        // prefixLen[data[firstIdx+suf]][data[firstIdx+suf+1]].insert(2);
        compLen[prevLCM] = prevLCM - (firstIdx+suf) + 2;
        prevLCM = firstIdx+suf;
      }
    }
  }
  
  // Pack the LCM suffixes at the beginning of SA to improve cache friendliness
  // Consider also packing the start indexes of each group at the end of SA

  SA[0] = dataSize;

  int packedTailIdx = dataSize+1;
  int packedHeadIdx = 1;
  for (int i = 0; i < 256; i++) {
    if (buckets[i] == 0) continue;
    for (int j = 0; j < 256; j++) {
      int groupLen = tails_d[i][j] - tailsIdx_d[i][j];
      if (groupLen == 0) continue;
      // for (int k = 0; k < groupLen; k++) {
      //   printf("%d, ", SA[tailsIdx_d[i][j]+1+k]);
      // }
      // printf("\n");
      std::copy(&SA[tailsIdx_d[i][j]]+1, &SA[tails_d[i][j]]+1, SA+packedHeadIdx);
      finalSA[packedTailIdx] = groupLen;
      packedTailIdx--;
      packedHeadIdx += groupLen;
    }
  }

  // All LCM suffix double buckets must be fully populated with non-LCM dupes for accuracy
  // This will enable the true detection of positionally relevant suffixes
  // for (int i = dataSize; i --> 0;) {
    // // 2-byte combos occuring only once provide free relative context
    // if (!lcmget(i) && tget_global(i) && !tget_global(i-1) && buckets_d[data[i]][data[i+1]] == 1) {
    //   lcmset(i, 1);
    //   SA[tailsIdx_d[data[i]][data[i+1]]] = i;
    //   tailsIdx_d[data[i]][data[i+1]]--;
    //   // compLen[i] = 2;
    //   // lset_global(i, 1);
    // }
    // if (!lcmget(i)
    //   && tailsIdx_d[data[i]][data[i+1]] != tails_d[data[i]][data[i+1]]
    // ) {
    //   lcmset(i, 1);
    //   SA[tailsIdx_d[data[i]][data[i+1]]] = i;
    //   tailsIdx_d[data[i]][data[i+1]]--;
    //   // lset_global(i, 1);
    //   // prefixLen[data[i]][data[i+1]].insert(NAIVESORT_CONST);
    //   // compLen[i] = 2;
    // }
  // }

  // for (int i = 0; i < packedHeadIdx; i++) {
  //   printf("%d, ", SA[i]);
  // }
  // printf("\n");

  // return;

  // lset_global(dataSize, 1);

  int packedSuf = 0;
  __builtin_prefetch(&data[dataSize-compLen[dataSize]], 0, 3);
  LCM[0] = dataSize;
  for (int d = 1; d < dataSize; d++) {
    if (lcmget(dataSize-d)) break;
    packedSuf = 0 |(dataSize-d) | (1 << 17);

    LCM[headsIdx_d[data[dataSize-d]][data[dataSize-d+1]]] = packedSuf;

    headsIdx_d[data[dataSize-d]][data[dataSize-d+1]]++;
  }

  int lastPos = -1;
  int lastSlot = -1;
  int saKey = -1;
  unsigned char commonCount = 0;
  int newData;
  
  int rootSortCount = 0;
  int currentIdx = 1;

  for (int i = dataSize+1; i > packedTailIdx; i--) {
    // printf("currentIdx: %d\n", currentIdx);
    // for (int j = 0; j < SA[i]; j++) {
    //   printf("%d, ", SA[currentIdx+j]);
    // }
    // printf("\n");
    if (finalSA[i] == 1) goto induction;
    if (SA[currentIdx] + 16 < dataSize) __builtin_prefetch(&SA[currentIdx]+16, 0, 3);

    insertionSufSort32(&SA[currentIdx], finalSA[i], [&](int sA, int sB) {
      if (sA+2 >= dataSize || sB+2 >= dataSize) {
        return sA < sB ? -1 : 1;
      }
      int r = memcmp(&data[sA+2], &data[sB+2], std::min(dataSize-sA, dataSize-sB));
      if (r == 0) return sA < sB ? -1 : 1;
      return r;
    });

    // insertionSufSort(&SA[currentIdx], finalSA[i], [&](int sA, int sB) {
    //   if (sA+2 >= dataSize || sB+2 >= dataSize) {
    //     return sA < sB ? -1 : 1;
    //   }
    //   int r = memcmp(&data[sA+2], &data[sB+2], std::min(dataSize-sA, dataSize-sB));
    //   if (r == 0) return sA < sB ? -1 : 1;
    //   return r;
    // });

    rootSortCount++;

    induction:

    saKey = SA[currentIdx];
    lastPos = saKey%chunkSize;
    lastSlot = 0;
    commonCount = 1;

    for (int k = currentIdx+1; k <= currentIdx+finalSA[i]; k++) {
      if (k > currentIdx+finalSA[i] || lastPos != SA[k]%chunkSize || compLen[SA[k]] != compLen[saKey]) {
        // __builtin_prefetch(&data[saKey-compLen[saKey]], 0, 3);

        LCM[headsIdx_d[data[saKey]][data[saKey+1]]] = (saKey) | ((uint64_t)commonCount << 17) | ((uint64_t)lastSlot << 25) | ((uint64_t)currentIdx << 33);
        // packedBucketHeadIndexes[saKey] = currentIdx;
        headsIdx_d[data[saKey]][data[saKey+1]]++;
        // printf("common %d, bucket count: %d\n", commonCount, finalSA[i]);
        for (uint64_t d = 1; d < dataSize; d++) {
          if (d > saKey) break;
          if (lcmget(saKey-d)) break;

          packedSuf = (saKey-d) | ((uint64_t)commonCount << 17) | ((uint64_t)(k - currentIdx) << 25) | ((uint64_t)currentIdx << 33) | (d << 41);
          LCM[headsIdx_d[data[saKey-d]][data[saKey-d+1]]] = packedSuf;
          // packedBucketHeadIndexes[saKey-d] = currentIdx;
          // packedBucketHeadOffsets[saKey-d] = d;
          // packedBucketHeadIndexes[(unsigned char)(unsigned char(data[saKey-d]) << 8 | data[saKey-d+1])] = packedHeadIdx;
          headsIdx_d[data[saKey-d]][data[saKey-d+1]]++;
        }
        saKey = SA[k];
        lastPos = SA[k]%chunkSize;
        lastSlot = k - currentIdx;
        commonCount = 0;
      }
      commonCount++;
    }
    currentIdx += finalSA[i];
  }

  // Re-pack the reduced/compressed suffix array for sorting
  packedTailIdx = dataSize+1;
  packedHeadIdx = 1;
  for (int i = 0; i < 256; i++) {
    if (buckets[i] == 0) continue;
    for (int j = 0; j < 256; j++) {
      int groupLen = headsIdx_d[i][j] - heads_d[i][j];
      if (groupLen == 0) continue;
      // for (int k = 0; k < groupLen; k++) {
      //   printf("%d, ", SA[tailsIdx_d[i][j]+1+k]);
      // }
      // printf("\n");
      std::copy(&LCM[heads_d[i][j]], &LCM[headsIdx_d[i][j]], LCM+packedHeadIdx);
      finalSA[packedTailIdx] = groupLen;
      packedTailIdx--;
      packedHeadIdx += groupLen;
    }
  }

  // for (int i = 0; i < 256; i++) {
  //   if (buckets[i] == 0) continue;
  //   for (int j = 0; j < 256; j++) {
  //     if (buckets_d[i][j] == 0) continue;
  //     saKey = SA[tailsIdx_d[i][j]+1];
  //     lastPos = saKey%chunkSize;
  //     lastSlot = 0;
  //     commonCount = 1;
  //     for (int k = tailsIdx_d[i][j]+2; k <= tails_d[i][j]+1; k++) {
  //       if (k > tails_d[i][j] || lastPos != SA[k]%chunkSize || compLen[SA[k]] != compLen[saKey]) {
  //         __builtin_prefetch(&data[saKey-compLen[saKey]], 0, 3);
  //         if (saKey == SA[tailsIdx_d[i][j]+1]) {
  //           LCM[headsIdx_d[data[saKey]][data[saKey+1]]] = (saKey) | (commonCount << 17) | (lastSlot << 25);
  //           rootHead[saKey] = heads_d[data[saKey]][data[saKey+1]];
  //           headsIdx_d[data[saKey]][data[saKey+1]]++;
  //         }
  //         // printf("common %d, bucket count: %d\n", commonCount, tails_d[i][j] - tailsIdx_d[i][j]);
  //         for (int d = 1; d < dataSize; d++) {
  //           if (saKey-d < 0) break;
  //           if (lcmget(saKey-d)) break;

  //           packedSuf = (saKey-d) | (commonCount << 17) | ((k - heads_d[i][j]) << 25);
  //           LCM[headsIdx_d[data[saKey-d]][data[saKey-d+1]]] = packedSuf;
  //           rootHead[saKey-d] = heads_d[data[saKey]][data[saKey+1]];

  //           headsIdx_d[data[saKey-d]][data[saKey-d+1]]++;
  //         }
  //         saKey = SA[k];
  //         lastPos = SA[k]%chunkSize;
  //         lastSlot = k - heads_d[i][j];
  //         commonCount = 0;
  //       }
  //       commonCount++;
  //     }
  //   }
  // }

  // for (int i = 0; i < 256; i++) {
  //   if (buckets[i] == 0) continue;
  //   for (int j = 0; j < 256; j++) {
  //     if (buckets_d[i][j] == 0) continue;
  //     saKey = SA[tailsIdx_d[i][j]+1];
  //     lastPos = saKey%chunkSize;
  //     lastSlot = 0;
  //     commonCount = 1;
  //     for (int k = tailsIdx_d[i][j]+2; k <= tails_d[i][j]+1; k++) {
  //       if (k > tails_d[i][j] || lastPos != SA[k]%chunkSize || compLen[SA[k]] != compLen[saKey]) {
  //         __builtin_prefetch(&data[saKey-compLen[saKey]], 0, 3);
  //         if (saKey == SA[tailsIdx_d[i][j]+1]) {
  //           LCM[headsIdx_d[data[saKey]][data[saKey+1]]] = (saKey) | (commonCount << 17) | (lastSlot << 25);
  //           rootHead[saKey] = heads_d[data[saKey]][data[saKey+1]];
  //           headsIdx_d[data[saKey]][data[saKey+1]]++;
  //         }
  //         // printf("common %d, bucket count: %d\n", commonCount, tails_d[i][j] - tailsIdx_d[i][j]);
  //         for (int d = 1; d < dataSize; d++) {
  //           if (saKey-d < 0) break;
  //           if (lcmget(saKey-d)) break;

  //           packedSuf = (saKey-d) | (commonCount << 17) | ((k - heads_d[i][j]) << 25);
  //           LCM[headsIdx_d[data[saKey-d]][data[saKey-d+1]]] = packedSuf;
  //           rootHead[saKey-d] = heads_d[data[saKey]][data[saKey+1]];

  //           headsIdx_d[data[saKey-d]][data[saKey-d+1]]++;
  //         }
  //         saKey = SA[k];
  //         lastPos = SA[k]%chunkSize;
  //         lastSlot = k - heads_d[i][j];
  //         commonCount = 0;
  //       }
  //       commonCount++;
  //     }
  //   }
  // }

  // for (int i = 0; i < 256; i++) {
  //   if (buckets[i] == 0) continue;
  //   for (int j = 0; j < 256; j++) {
  //     if (buckets_d[i][j] == 0) continue;
  //     if (tails_d[i][j] - tailsIdx_d[i][j] > 1) {
  //       __builtin_prefetch(&data[LCM[tailsIdx_d[i][j]+1]], 0, 3);
        
  //       // printf("bucket: %02X %02X\n", i, j);
  //       // printf("common prefix lengths: ");
  //       // for (int k : prefixLen[i][j]) {
  //       //   printf("%d, ", k);
  //       // }
  //       // printf("\nsuffix count: %d", tails_d[i][j] - tailsIdx_d[i][j]);
  //       // printf("\n\n");

  //       // int it = 0;
  //       // for(int prefLen : prefixLen[i][j]) {
  //       //   if (prefLen == NAIVESORT_CONST) {
  //       //     std::sort(&SA[tailsIdx_d[i][j]+1], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //       //       return memcmp(&data[sA+2], &data[sB+2], dataSize) < 0;
  //       //     });
  //       //     break;
  //       //   } else if (i == 0 && j == 0)
  //       //     std::stable_sort(&SA[tailsIdx_d[i][j]+1], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //       //       if (compLen[sA] != prefLen) return false;
  //       //       if (compLen[sB] != prefLen) return true;
  //       //       return sA + prefLen >= dataSize || memcmp(&data[sA+prefLen], &data[sB+prefLen], dataSize) < 0;
  //       //     });
  //       //   else if (it > 0) {
  //       //     std::stable_sort(&SA[tailsIdx_d[i][j]+1], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //       //       if (compLen[sA] != prefLen) return false;
  //       //       if (compLen[sB] != prefLen) return true;
  //       //       return sA + prefLen >= dataSize || data[sA+prefLen] < data[sB+prefLen];
  //       //     });
  //       //   } else {
  //       //     std::sort(&SA[tailsIdx_d[i][j]+1], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //       //       if (compLen[sA] != prefLen) return false;
  //       //       if (compLen[sB] != prefLen) return true;
  //       //       return sA + prefLen >= dataSize || data[sA+prefLen] < data[sB+prefLen];
  //       //     });
  //       //   }
  //       //   it++;
  //       // }


  //       int cp = 0;
  //       std::sort(&SA[tailsIdx_d[i][j]]+1, &SA[tails_d[i][j]]+1, [&](int sA, int sB) {
  //         return memcmp(&data[sA+2], &data[sB+2], dataSize) < 0;
  //         // cp = std::min(compLen[sA], compLen[sB]);
  //         // return data[sA+cp] < data[sB+cp];
  //       });
  //     }
  //   }
  // }
  auto end = std::chrono::steady_clock::now();

  /* 
  Instead of writing all offsets to all buckets, do this.
  Within each sorted bucket, record the suffix at said position.
  Afterwards, move forward within the bucket until the root suffix value or position changes.
  Once this is found to be the case, count the total suffixes before said change.
  Then, pack the value into an integer, with the unshifted value being the original suffix,
  the count being packed << 17, and the position within the bucket being packed << 25.
  Cascade/copy backward into the head of each prefix position this packed value - distance.

  After this, sort the packed suffix headers lexicographically using data from the stored suffix position.
  Once this is done, iterate over all buckets, copying the necessary suffix groups in their
  induced order into the final array (with SIMD if possible), referencing the original bucket positions 
  and offsets.
  */

  auto start2 = std::chrono::steady_clock::now();

  auto end2 = std::chrono::steady_clock::now();

  auto time4 = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  // // std::cout << "my packed test" << std::endl;
  // for (int i = 1; i < dataSize+1; i++) {
  //   // if (tget_global(SA[i]) && !tget_global(SA[i]-1)) {
  //   // if (lcmget(SA[i])) {
  //     if ((LCM[i] & 0x1FFFF) == (-1 & 0x1FFFF)) std::cout << "-, ";
  //     else std::cout << (int)(LCM[i] & 0x1FFFF) 
  //     // Line below prints suffix reduction info
  //     << "/" << (int)((LCM[i] >> 17) & 0xFF) << "->" <<  (int)((LCM[i] >> 25) & 0xFF) 
  //     << ", ";
  //   // }
  // }
  // std::cout << std::endl;
  // printf("\n");

  // printf("My Setup took %.6f seconds\n", (double)time4.count()/1000000000.0);

  // return;

  // OLD METHOD BELOW
  
  // for (int d = 1; d < dataSize; d++) {
  //   if (tget_local(dataSize)) goto after;
  //   if (d > 0 && lcmget(dataSize-d)) {tset_local(dataSize, 1); goto after;}
    
  //   lset_global(dataSize-d, 1);
  //   LCM[headsIdx_d[data[dataSize-d]][data[dataSize-d+1]]] = dataSize-d;
  //   inferenceDist[dataSize-d] = d;

  //   int& depth = inductionData[data[dataSize-d]][data[dataSize-d+1]];
  //   int& root = rootBytes[data[dataSize-1]][0];

  //   if (depth == -1) {
  //     depth = d;
  //     depth = *(unsigned char*)(&data[dataSize-1]);
  //   } else if (depth != d) {
  //     depth = -2;
  //   }

  //   if (root == -1) {
  //     root = data[dataSize-1] << 16;
  //   } else if (root != data[dataSize-1] << 16) {
  //     root = -2;
  //   }

  //   headsIdx_d[data[dataSize-d]][data[dataSize-d+1]]++;
  // }

  // after:

  // for (int i = 0; i < 256; i++) {
  //   for (int j = 0; j < 256; j++) {
  //     for (int d = 1; d < dataSize; d++) {
  //       bool found = false;
  //       for (int k = tailsIdx_d[i][j]+1; k < tails_d[i][j]+1; k++) {
  //         if (tget_local(SA[k]) || SA[k]-d < 0) continue;
  //         if (d > 0 && lcmget(SA[k]-d)) {tset_local(SA[k], 1); sortCount[i][j]++; continue;}
  //         found = true;
  //         lset_global(SA[k]-d, 1);
  //         if (d == 1) {
  //           SA[headsIdx_d[data[SA[k]-d]][i]] = SA[k]-d;
  //           inferenceDist[SA[k]-d] = d;

  //           int& depth = inductionData[data[SA[k]-d]][i];
  //           int& root = rootBytes[data[SA[k]-d]][i];

  //           if (depth == -1) {
  //             depth = d;
  //           } else if (depth != d) {
  //             depth = -2;
  //           }

  //           if (root == -1) {
  //             root = (i << 16) | j;
  //           } else if (root != data[dataSize-1] << 16) {
  //             root = -2;
  //           }

  //           headsIdx_d[data[SA[k]-d]][i]++;
  //         } else {
  //           SA[headsIdx_d[data[SA[k]-d]][data[SA[k]-d+1]]] = SA[k]-d;
  //           inferenceDist[SA[k]-d] = d;

  //           int& depth = inductionData[data[SA[k]-d]][data[SA[k]-d+1]];
  //           int& root = rootBytes[data[SA[k]-d]][data[SA[k]-d+1]];

  //           if (depth == -1) {
  //             depth = d;
  //           } else if (depth != d) {
  //             depth = -2;
  //           }

  //           if (root == -1) {
  //             root = (i << 16) | j;
  //           } else if (root != data[dataSize-1] << 16) {
  //             root = -2;
  //           }
            
  //           headsIdx_d[data[SA[k]-d]][data[SA[k]-d+1]]++;
  //         }
  //       }
  //       if (!found) break;
  //     }
  //   }
  // }
  
  auto start3 = std::chrono::steady_clock::now();
  // Need to optimize this sort to work with ranked groups. Should be possible
  int sortCount = 0;
  currentIdx = 1;
  int finalIdx = 1;
  for (int i = dataSize+1; i > packedTailIdx; i--) {
    // for (int j = 0; j < SA[i]; j++) {
    //   printf("%d, ", SA[currentIdx+j]);
    // }
    // printf("\n");
    if (finalSA[i] == 1) goto copy;
    // if (data[(LCM[currentIdx] & 0x1FFFF)+1] == 0) goto copy;
    if (LCM[currentIdx] + 16 < dataSize) __builtin_prefetch(&LCM[currentIdx]+16, 0, 3);

    // printf("NEW GROUP\n");

    insertionSufSort(&LCM[currentIdx], finalSA[i], [&](uint64_t psA, uint64_t psB) {
      int sA = psA & 0x1FFFF;
      int sB = psB & 0x1FFFF;
      if ((sA % chunkSize == sB % chunkSize && ((psA >> 41) & 0x3FF) == ((psB >> 41) & 0x3FF)) 
        || (lcmget(sA) && lcmget(sB))) return 1;
      // printf("comparison between:\n");
      // bool foundRoot = false;
      // for (int j = 0; j < dataSize; j++) {
      //   if (!foundRoot && lcmget(sA+j)) printf("ROOT-> ");
      //   printf("%02X ", data[sA+j]);
      //   if (!foundRoot && lcmget(sA+j)) {printf("<-ROOT "); foundRoot = true;}
      //   if (data[sA+j] != data[sB+j]) break;
      // }
      // printf("\n\n");
      // foundRoot = false;
      // for (int j = 0; j < dataSize; j++) {
      //   if (!foundRoot && lcmget(sB+j)) printf("ROOT-> ");
      //   printf("%02X ", data[sB+j]);
      //   if (!foundRoot && lcmget(sB+j)) {printf("<-ROOT "); foundRoot = true;}
      //   if (data[sA+j] != data[sB+j]) break;
      // }
      // printf("\n\n\n");
      if (sA+2 >= dataSize || sB+2 >= dataSize) {
        int r = sA < sB ? -1 : 1;
        if (r < 0) sortCount++;
        return r;
      }
      int r = memcmp(&data[sA+2], &data[sB+2], std::min(dataSize-sA, dataSize-sB));
      if (r == 0) return sA < sB ? -1 : 1;
      if (r < 0) sortCount++;
      return r;
    });

    copy:
    for (int j = 0; j < finalSA[i]; j++) {      
      bool foundKey = false;
      for (int k = 0; k < chunkSize; k++) {
        if (lcmget((LCM[currentIdx+j] & 0x1FFFF))) printf("ROOT-> ");
        printf("%02X ", data[(LCM[currentIdx+j] & 0x1FFFF)+k]);
        if (lcmget((LCM[currentIdx+j] & 0x1FFFF))) printf("<-ROOT ");
        if (j%2 == 0) {
          if (!foundKey && k > 0 && data[(LCM[currentIdx+j] & 0x1FFFF)+k] != data[(LCM[currentIdx+j-1] & 0x1FFFF)+k]){
            printf("<-KEY ");
            foundKey = true;
          }
          if (k > 0 && data[(LCM[currentIdx+j] & 0x1FFFF)+k] != data[(LCM[currentIdx+j+1] & 0x1FFFF)+k]) {
            break;
          }
        }
        else if (k > 0 && data[(LCM[currentIdx+j] & 0x1FFFF)+k] != data[(LCM[currentIdx+j-1] & 0x1FFFF)+k]) break;
      }
      printf("\n");
    }
    printf("\n\n");
    // for (int j = 0; j < ((LCM[currentIdx+j] >> 17) & 0xFF); j++) {      
    //   int unpackedSuf = LCM[currentIdx+j] & 0x1FFFF;
    //   int groupHead = packedBucketHeadIndexes[unpackedSuf+packedBucketHeadOffsets[unpackedSuf]];
    //   // printf("new copy instance\n");
    //   // for (int j = 0; j < ((LCM[i] >> 17) & 0xFF); j++) {
    //   //   // printf("packed read index: %d, found suffix: ", groupHead + j);
    //   //   // printf("%d\n", SA[groupHead + ((LCM[i] >> 25) & 0xFF) + j] - offset);
    //   //   // finalSA[finalIdx] = SA[groupHead + ((LCM[i] >> 25) & 0xFF) + j] - offset;
    //   //   finalIdx++;
    //   // }
    //   // maxOffset = std::max(maxOffset, packedBucketHeadOffsets[unpackedSuf]);
    //   std::copy(&SA[groupHead], &SA[groupHead]+((LCM[currentIdx+j] >> 17) & 0xFF), &finalSA[currentIdx+j]);
    //   for (int k = finalIdx; k - finalIdx < ((LCM[currentIdx+j] >> 17) & 0xFF); k++) {
    //     finalSA[k] -= packedBucketHeadOffsets[unpackedSuf];
    //   }
    //   finalIdx += ((LCM[currentIdx+j] >> 17) & 0xFF);

    //   // printf("\n");
    // }

    currentIdx += finalSA[i];
  }
  // for (int i = 0; i < 256; i++) {
  //   for (int j = 0; j < 256; j++) {
  //     if (buckets_d[i][j] == 0) continue;
  //     // if (j < 255) __builtin_prefetch(&LCM[heads_d[i][j+1]],0,3);
  //     // if (headsIdx_d[i][j] - heads_d[i][j] == 0) {
  //     //   if (buckets_d[i][j] == 1) printf("singular token ");
  //     //   printf("oh noooooo! %02X %02X\n", i, j);
  //     // }
  //     // printf("sort size: %d\n", headsIdx_d[i][j] - heads_d[i][j]);
  //     int sortLen = headsIdx_d[i][j] - heads_d[i][j];
  //     if (headsIdx_d[i][j] - heads_d[i][j] > 1) {
  //       int comps = 0;
  //       insertionSufSortB(&LCM[heads_d[i][j]], sortLen, [&](int psA, int psB) {
  //         int sA = psA & 0x1FFFF;
  //         int sB = psB & 0x1FFFF;
  //         comps++;
  //         int r = memcmp(&data[sA+2], &data[sB+2], std::min(dataSize-sA, dataSize-sB));
  //         if (r == 0) return sA < sB ? -1 : 1;
  //         return r;
  //       });
  //       // printf("%d comparisons to sort %d suffix groups\n", comps, sortLen);
  //       // std::sort(&LCM[heads_d[i][j]], &LCM[headsIdx_d[i][j]+1], [&](int sA, int sB) {
  //       //   return sA + 2 >= dataSize+1 || memcmp(&data[sA+2], &data[sB+2], dataSize) < 0;
  //       // });
  //       sortCount++;
  //     }
  //   }
  // }
  auto end3 = std::chrono::steady_clock::now();

  auto start4 = std::chrono::steady_clock::now();
  // int finalIdx = 1;
  int currentTally = 0;
  unsigned char maxOffset = 0;
  for (int i = 1; i < packedHeadIdx; i++) {
    __builtin_prefetch(&LCM[i]+64, 0, 3);
    
    int unpackedSuf = LCM[i] & 0x1FFFF;
    int groupHead = packedBucketHeadIndexes[(LCM[i] >> 33) & 0xFF]+(LCM[i] >> 25)& 0xFF;;
    // printf("new copy instance\n");
    // for (int j = 0; j < ((LCM[i] >> 17) & 0xFF); j++) {
    //   // printf("packed read index: %d, found suffix: ", groupHead + j);
    //   // printf("%d\n", SA[groupHead + ((LCM[i] >> 25) & 0xFF) + j] - offset);
    //   // finalSA[finalIdx] = SA[groupHead + ((LCM[i] >> 25) & 0xFF) + j] - offset;
    //   finalIdx++;
    // }
    // maxOffset = std::max(maxOffset, packedBucketHeadOffsets[unpackedSuf]);
    // printf("group size: %d\n", ((LCM[i] >> 17) & 0xFF));
    std::copy(&SA[groupHead], &SA[groupHead]+((LCM[i] >> 17) & 0xFF), &finalSA[finalIdx]);
    for (int j = finalIdx; j - finalIdx < ((LCM[i] >> 17) & 0xFF); j++) {
      finalSA[j] -= packedBucketHeadOffsets[unpackedSuf];
    }
    // if (finalSA[finalIdx]+1 < dataSize && data[finalSA[finalIdx]+1] == 0) {

    // }
    finalIdx += ((LCM[i] >> 17) & 0xFF);

    // printf("\n");
  }
  auto end4 = std::chrono::steady_clock::now();

  printf("%d root sort operations performed\n", rootSortCount);
  printf("%d reduction sort operations performed\n", sortCount);
  // printf("maxOffset: %d\n", maxOffset);

  // OLD method below

  // // Need to optimize this sort to work with ranked groups. Should be possible
  // for (int i = 0; i < 256; i++) {
  //   for (int j = 0; j < 256; j++) {
  //     if (inductionData[i][j] == -2) {
  //       __builtin_prefetch(&data[SA[heads_d[i][j]]], 0, 3);
  //       // Sort the double bucket using LCP information
  //       // int it = 0;
  //       // for (int prefLen : prefixLen[i][j]) {
  //       //   if (prefLen == NAIVESORT_CONST) {
  //       //     std::sort(&SA[heads_d[i][j]], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //       //       return sA+1 >= dataSize || memcmp(&data[sA+2], &data[sB+2], dataSize) < 0;
  //       //     });
  //       //     break;
  //       //   } else if (i == 0 && j == 0) {
  //       //     std::stable_sort(&SA[heads_d[i][j]], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //       //       return sA + prefLen >= dataSize || memcmp(&data[sA+prefLen], &data[sB+prefLen], dataSize) < 0;
  //       //     });
  //       //   } else if (it > 0) {
  //       //     std::stable_sort(&SA[heads_d[i][j]], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //       //       return sA + prefLen >= dataSize || data[sA+prefLen] < data[sB+prefLen];
  //       //     });
  //       //   } else {
  //       //     // printf("prefLen = %d\n", prefLen);
  //       //     std::sort(&SA[heads_d[i][j]], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //       //       return sA + prefLen >= dataSize || data[sA+prefLen] < data[sB+prefLen];
  //       //     });
  //       //   }
  //       //   it++;
  //       // }
  //       std::sort(&SA[heads_d[i][j]], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //         return memcmp(&data[sA+2], &data[sB+2], dataSize) < 0;
  //       });
  //     }
  //     if (rootBytes[i][j] == -2) {
  //       std::stable_sort(&SA[heads_d[i][j]], &SA[tails_d[i][j]+1], [&](int sA, int sB) {
  //         return data[sA+2] < data[sB+2];
  //       });
  //     }
  //   }
  // }

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

  auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);

  auto time2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2-start2);

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

  printf("My Setup took %.6f seconds, (deprecated) LCM induction took %.6f seconds\n", (double)time.count()/1000000000.0, (double)time2.count()/1000000000.0);
  time = std::chrono::duration_cast<std::chrono::nanoseconds>(end3-start3);
  printf("Reduced sort took %.6f seconds\n", (double)time.count()/1000000000.0);
  time = std::chrono::duration_cast<std::chrono::nanoseconds>(end4-start4);
  printf("Final copy took %.6f seconds\n", (double)time.count()/1000000000.0);

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

  // std::cout << "my output" << std::endl;
  // for (int i = 1; i < dataSize+1; i++) {
  //   // if (tget_global(SA[i]) && !tget_global(SA[i]-1)) {
  //   // if (lcmget(SA[i])) {
  //   std::cout << (int)finalSA[i] << ", ";
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

  // printf("\n");
  // std::cout << "\nSA inaccuracies" << std::endl;
  // for (int i = 0; i < dataSize; i++) {
  //   // if (SA[i+1] != DSS_SA[i]) {
  //   //   printf("index: %d, suffix: %d, expected suffix: %d, inferenceDist: %d, in-chunk pos: %d\n", i+1, SA[i+1], DSS_SA[i], inferenceDist[SA[i+1]], SA[i+1]%chunkSize);
  //   //   printf("root double bucket: %02X %02X, root in-chunk pos: %d\n", data[SA[i+1]+inferenceDist[SA[i+1]]], data[SA[i+1]+inferenceDist[SA[i+1]]+1], (SA[i+1]+inferenceDist[SA[i+1]])%chunkSize);
  //   //   // printf("comp in-chunk: %d, comp spot: %d, comp double bucket %02X %02X\n", compLen[SA[i+1]+inferenceDist[SA[i+1]]]%chunkSize, compLen[SA[i+1]+inferenceDist[SA[i+1]]], data[compLen[SA[i+1]+inferenceDist[SA[i+1]]]], data[compLen[SA[i+1]+inferenceDist[SA[i+1]]]+1]);
  //   //   // for (int j = 0; j < compLen[SA[i+1]+inferenceDist[SA[i+1]]]+2; j++) {
  //   //   for (int j = 0; j < chunkSize; j++) {
  //   //     printf("%02X ", data[SA[i+1]+j]);
  //   //   }
  //   //   printf("\n\n");
  //   // }
  //   if (SA[i+1] != DSS_SA[i]) {
  //     std::cout << SA[i+1]%chunkSize << ", ";
  //   } else {
  //     std::cout << "-" << ", ";
  //   }
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

  printf("size: %d\n", size);

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