#pragma once

#include <vector>
#include <cstring>
#include <string>

typedef struct LMSInfo {
    int rank;
    int len;
    std::vector<int> suffixPositions;
} LMSInfo;

std::string terminator("You'll Never Find Me $$$");

unsigned char data1[] = {
    // Chunk 1
    0x5A, 0x3F, 0x2C, 0x81, 0x6E, 0x94, 0x7B, 0xD2, 0x8F, 0x10, 0x4D, 0x3C, 0x29, 0x81, 0x6A, 0x90,
    0x7F, 0xD6, 0x8B, 0x14, 0x49, 0x38, 0x2D, 0x85, 0x6E, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0xA7,
    // Chunk 2
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x7F, 0xD2, 0x8F, 0x10, 0x4D, 0x3C, 0x29, 0x81, 0x6A, 0x90,
    0x7F, 0xD6, 0x8B, 0x14, 0x49, 0x38, 0x2D, 0x85, 0x6E, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0x1C,
    // Chunk 3
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x7F, 0xD2, 0x83, 0x1C, 0x51, 0x3C, 0x29, 0x81, 0x6A, 0x90,
    0x7F, 0xD6, 0x8B, 0x14, 0x49, 0x38, 0x2D, 0x85, 0x6E, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0x62,
    // Chunk 4
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x7F, 0xD2, 0x83, 0x1C, 0x51, 0x3C, 0x29, 0x81, 0x6A, 0x90,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x38, 0x2D, 0x85, 0x6E, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0x3F,
    // Chunk 5
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x7F, 0xD2, 0x83, 0x1C, 0x51, 0x3C, 0x29, 0x81, 0x6A, 0x90,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x38, 0x2D, 0x85, 0x6E, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0x3F,
    // Chunk 6
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x7F, 0xD2, 0x83, 0x1C, 0x51, 0x38, 0x25, 0x85, 0x6A, 0x90,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x38, 0x2D, 0x85, 0x6E, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0xF1,
    // Chunk 7
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x7F, 0xD2, 0x83, 0x1C, 0x51, 0x38, 0x25, 0x85, 0x6A, 0x90,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x62, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0x2E,
    // Chunk 8
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x7F, 0xD2, 0x83, 0x1C, 0x51, 0x38, 0x25, 0x85, 0x6A, 0x90,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x62, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0x8C,
    // Chunk 9
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x38, 0x25, 0x85, 0x6A, 0x90,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x62, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0xB5,
    // Chunk 10
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6A, 0x90,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x62, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0x79,
    // Chunk 11
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x62, 0x94, 0x73, 0xD2, 0x8F, 0x18, 0x4D, 0xD4,
    // Chunk 12
    0x5A, 0x3F, 0x2C, 0x81, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6A, 0x98, 0x7F, 0xD2, 0x8F, 0x18, 0x4D, 0x53,
    // Chunk 13
    0x5A, 0x3B, 0x28, 0x85, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6A, 0x98, 0x7F, 0xD2, 0x8F, 0x18, 0x4D, 0xC6,
    // Chunk 14
    0x5A, 0x3B, 0x28, 0x85, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6A, 0x98, 0x7F, 0xD2, 0x8F, 0x1C, 0x51, 0x9A,
    // Chunk 15
    0x5A, 0x3B, 0x28, 0x85, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6A, 0x98, 0x7F, 0xD2, 0x8F, 0x1C, 0x51, 0x7D,
    // Chunk 16
    0x5A, 0x3B, 0x28, 0x85, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6A, 0x98, 0x7F, 0xD2, 0x8F, 0x1C, 0x51, 0x11,
    // Chunk 17
    0x5A, 0x3B, 0x28, 0x85, 0x62, 0x98, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6A, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x6C,
    // Chunk 18
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6A, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0xBF,
    // Chunk 19
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x1C, 0x51, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x42,
    // Chunk 20
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0xED,
    // Chunk 21
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x3B,
    // Chunk 22
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x6E, 0x98,
    0x73, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x96,
    // Chunk 23
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x66,0x98,
    0x73, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x59,
    // Chunk 24
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x66, 0x98,
    0x7B, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0xC2,
    // Chunk 25
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x66, 0x98,
    0x7B, 0xDA, 0x87, 0x18, 0x45, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x8F,
    // Chunk 26
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x66, 0x98,
    0x7B, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x75,
    // Chunk 27
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x66, 0x98,
    0x7B, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0xD8,
    // Chunk 28
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x66, 0x98,
    0x77, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x2B,
    // Chunk 29
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x66, 0x98,
    0x77, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0xA3,
    // Chunk 30
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x29, 0x85, 0x66, 0x98,
    0x77, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x4E,
    // Chunk 31
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x25, 0x85, 0x66, 0x98,
    0x77, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0x1F,
    // Chunk 32
    0x5A, 0x3B, 0x28, 0x85, 0x66, 0x90, 0x77, 0xDE, 0x83, 0x14, 0x49, 0x34, 0x25, 0x85, 0x66, 0x98,
    0x77, 0xDA, 0x87, 0x18, 0x49, 0x3C, 0x29, 0x89, 0x6E, 0x98, 0x7F, 0xDE, 0x83, 0x1C, 0x51, 0xE2
};

unsigned char data2[] = {
    // Chunk 1
    90, 63, 44, 129, 110, 148, 123, 210, 143, 16, 77, 60, 41, 129, 106, 144,
    127, 214, 139, 20, 73, 56, 45, 133, 110, 148, 115, 210, 143, 24, 77, 167,
    // Chunk 2
    90, 63, 44, 129, 98, 152, 127, 210, 143, 16, 77, 60, 41, 129, 106, 144,
    127, 214, 139, 20, 73, 56, 45, 133, 110, 148, 115, 210, 143, 24, 77, 28,
    // Chunk 3
    90, 63, 44, 129, 98, 152, 127, 210, 131, 28, 81, 60, 41, 129, 106, 144,
    127, 214, 139, 20, 73, 56, 45, 133, 110, 148, 115, 210, 143, 24, 77, 98,
    // Chunk 4
    90, 63, 44, 129, 98, 152, 127, 210, 131, 28, 81, 60, 41, 129, 106, 144,
    115, 218, 135, 24, 73, 56, 45, 133, 110, 148, 115, 210, 143, 24, 77, 63,
    // Chunk 5
    90, 63, 44, 129, 98, 152, 127, 210, 131, 28, 81, 60, 41, 129, 106, 144,
    115, 218, 135, 24, 73, 56, 45, 133, 110, 148, 115, 210, 143, 24, 77, 77,
    // Chunk 6
    90, 63, 44, 129, 98, 152, 127, 210, 131, 28, 81, 56, 37, 133, 106, 144,
    115, 218, 135, 24, 73, 56, 45, 133, 110, 148, 115, 210, 143, 24, 77, 241,
    // Chunk 7
    90, 63, 44, 129, 98, 152, 127, 210, 131, 28, 81, 56, 37, 133, 106, 144,
    115, 218, 135, 24, 73, 60, 41, 137, 98, 148, 115, 210, 143, 24, 77, 46,
    // Chunk 8
    90, 63, 44, 129, 98, 152, 127, 210, 131, 28, 81, 56, 37, 133, 106, 144,
    115, 218, 135, 24, 73, 60, 41, 137, 98, 148, 115, 210, 143, 24, 77, 140,
    // Chunk 9
    90, 63, 44, 129, 98, 152, 119, 222, 131, 28, 81, 56, 37, 133, 106, 144,
    115, 218, 135, 24, 73, 60, 41, 137, 98, 148, 115, 210, 143, 24, 77, 181,
    // Chunk 10
    90, 63, 44, 129, 98, 152, 119, 222, 131, 28, 81, 52, 41, 133, 106, 144,
    115, 218, 135, 24, 73, 60, 41, 137, 98, 148, 115, 210, 143, 24, 77, 121,
    // Chunk 11
    90, 63, 44, 129, 98, 152, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 73, 60, 41, 137, 98, 148, 115, 210, 143, 24, 77, 212,
    // Chunk 12
    90, 63, 44, 129, 98, 152, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 73, 60, 41, 137, 106, 152, 127, 210, 143, 24, 77, 83,
    // Chunk 13
    90, 59, 40, 133, 98, 152, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 73, 60, 41, 137, 106, 152, 127, 210, 143, 24, 77, 198,
    // Chunk 14
    90, 59, 40, 133, 98, 152, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 73, 60, 41, 137, 106, 152, 127, 210, 143, 28, 81, 154,
    // Chunk 15
    90, 59, 40, 133, 98, 152, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 73, 60, 41, 137, 106, 152, 127, 210, 143, 28, 81, 125,
    // Chunk 16
    90, 59, 40, 133, 98, 152, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 69, 60, 41, 137, 106, 152, 127, 210, 143, 28, 81, 17,
    // Chunk 17
    90, 59, 40, 133, 98, 152, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 69, 60, 41, 137, 106, 152, 127, 222, 131, 28, 81, 108,
    // Chunk 18
    90, 59, 40, 133, 102, 144, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 69, 60, 41, 137, 106, 152, 127, 222, 131, 28, 81, 191,
    // Chunk 19
    90, 59, 40, 133, 102, 144, 119, 222, 131, 28, 81, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 69, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 66,
    // Chunk 20
    90, 59, 40, 133, 102, 144, 119, 222, 131, 20, 73, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 69, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 237,
    // Chunk 21
    90, 59, 40, 133, 102, 144, 119, 222, 131, 20, 73, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 69, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 59,
    // Chunk 22
    90, 59, 40, 133, 102, 144, 119, 222, 131, 20, 73, 52, 41, 133, 110, 152,
    115, 218, 135, 24, 69, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 150,
    // Chunk 23
    90, 59, 40, 133, 102, 144, 119, 222, 131, 20, 73, 52, 41, 133, 102, 152,
    115, 218, 135, 24, 69, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 89,
    // Chunk 24
    90, 59, 40, 133, 102, 144, 119, 222, 131, 20, 73, 52, 41, 133, 102, 152,
    123, 218, 135, 24, 69, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 194,
    // Chunk 25
    90, 59, 40, 133, 102, 144, 119, 222, 131, 20, 73, 52, 41, 133, 102, 152,
    123, 218, 135, 24, 69, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 143,
    // Chunk 26
    90, 59, 40, 133, 102, 144, 119, 222, 131, 20, 73, 52, 41, 133, 102, 152,
    123, 218, 135, 24, 73, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 117,
    // Chunk 27
    90, 59, 40, 133, 102, 144, 119, 222, 131, 20, 73, 52, 41, 133, 102, 152,
    123, 218, 135, 24, 73, 60, 41, 137, 110, 152, 127, 222, 131, 28, 81, 216,
    // Chunk 28
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    // Chunk 29
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    // Chunk 30
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    // Chunk 31
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    // Chunk 32
    1, 4, 1, 6, 12, 62, 255, 12, 15, 155, 163, 124, 125, 67, 27, 99,
    1, 4, 1, 6, 12, 62, 255, 12, 4, 12, 21, 36, 125, 67, 27, 99,
};

unsigned char data3[] = {
    // Chunk 1
    95, 58, 39, 142, 101, 167, 134, 219, 152, 31, 86, 71, 50, 142, 117, 155,
    136, 225, 148, 35, 82, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 188,
    // Chunk 2
    95, 58, 39, 142, 105, 163, 128, 219, 152, 31, 86, 71, 50, 142, 117, 155,
    136, 225, 148, 35, 82, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 49,
    // Chunk 3
    95, 58, 39, 142, 105, 163, 128, 219, 140, 23, 90, 71, 50, 142, 117, 155,
    136, 225, 148, 35, 82, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 83,
    // Chunk 4
    95, 58, 39, 142, 105, 163, 128, 219, 140, 23, 90, 67, 54, 142, 117, 155,
    136, 225, 148, 35, 82, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 2,
    // Chunk 5
    95, 58, 39, 142, 105, 163, 128, 219, 140, 23, 90, 67, 54, 142, 117, 155,
    136, 225, 148, 35, 82, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 86,
    // Chunk 6
    95, 58, 39, 142, 105, 163, 128, 219, 140, 23, 90, 67, 54, 148, 113, 155,
    136, 225, 148, 35, 82, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 222,
    // Chunk 7
    95, 58, 39, 146, 109, 163, 128, 219, 140, 23, 90, 67,54, 148, 113, 155,
    136, 225, 148, 35, 82, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 11,
    // Chunk 8
    95, 58, 39, 146, 109, 163, 128, 219, 140, 23, 90, 67, 54, 148, 113, 155,
    136, 225, 144, 31, 86, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 169,
    // Chunk 9
    95, 58, 39, 146, 109, 163, 128, 223, 136, 23, 90, 67, 54, 148, 113, 155,
    136, 225, 144, 31, 86, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 154,
    // Chunk 10
    95, 58, 39, 146, 109, 163, 128, 223, 136, 23, 90, 63, 58, 148, 113, 155,
    136, 225, 144, 31, 86, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 94,
    // Chunk 11
    95, 58, 39, 146, 109, 163, 128, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 86, 67, 54, 144, 101, 167, 124, 219, 152, 39, 86, 245,
    // Chunk 12
    95, 58, 39, 146, 109, 163, 128, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 86, 67, 54, 144, 97, 171, 128, 219, 152, 39, 86, 116,
    // Chunk 13
    99, 62, 43, 148, 109, 163, 128, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 86, 67, 54, 144, 97, 171, 128, 219, 152, 39, 86, 231,
    // Chunk 14
    99, 62, 43, 148, 109, 163, 128, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 86, 67, 54, 144, 97, 171, 128, 219, 152, 35, 94, 175,
    // Chunk 15
    99, 62, 43, 148, 109, 163, 128, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 86, 67, 54, 144, 97, 171, 128, 219, 152, 35, 94, 158,
    // Chunk 16
    99, 62, 43, 148, 109, 163, 128, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 78, 67, 54, 144, 97, 171, 128, 219, 152, 35, 94, 44,
    // Chunk 17
    99, 62, 43, 148, 109, 163, 128, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 78, 67, 54, 144, 97, 171, 128, 227, 140, 35, 94, 141,
    // Chunk 18
    99, 62, 43, 148, 113, 159, 124, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 78, 67, 54, 144, 97, 171, 128, 227, 140, 35, 94, 208,
    // Chunk 19
    99, 62, 43, 148, 113, 159, 124, 223, 136, 23, 90, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 78, 67, 54, 144, 109, 167, 128, 227, 140, 35, 94, 99,
    // Chunk 20
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 78, 67, 54, 144, 109, 167, 128, 227, 140, 35, 94, 14,
    // Chunk 21
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 78, 67, 54, 144, 109, 167, 128, 227, 140, 35, 94, 92,
    // Chunk 22
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 105, 167,
    136, 225, 144, 31, 78, 67, 54, 144, 109, 167, 128, 227, 140, 35, 94, 183,
    // Chunk 23
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 101, 163,
    136, 225, 144, 31, 78, 67, 54, 144, 109, 167, 128, 227, 140, 35, 94, 126,
    // Chunk 24
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 101, 163,
    132, 225, 144, 31, 78, 67, 54, 144, 109, 167, 128, 227, 140, 35, 94, 227,
    // Chunk 25
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 101, 163,
    132, 225, 144, 31, 78, 67, 58, 140, 109, 167, 128, 227, 140, 35, 94, 176,
    // Chunk 26
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 101, 163,
    132, 225, 144, 31, 82, 67, 58, 140, 109, 167, 128, 227, 140, 35, 94, 134,
    // Chunk 27
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 101, 163,
    132, 225, 144, 31, 82, 67, 58, 140, 109, 167, 128, 227, 140, 35, 94, 249,
    // Chunk 28
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 101, 163,
    128, 225, 144, 31, 82, 67, 58, 140, 109, 167, 128, 227, 140, 35, 94, 60,
    // Chunk 29
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 101, 163,
    128, 225, 144, 31, 82, 67, 58, 140, 109, 167, 128, 227, 140, 35, 94, 196,
    // Chunk 30
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 58, 148, 101, 163,
    128, 225, 144, 31, 82, 67, 58, 140, 109, 167, 128, 227, 140, 35, 94, 111,
    // Chunk 31
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 62, 148, 101, 163,
    128, 225, 144, 31, 82, 67, 58, 140, 109, 167, 128, 227, 140, 35, 94, 48,
    // Chunk 32
    99, 62, 43, 148, 113, 159, 124, 223, 136, 27, 82, 63, 62, 148, 101, 163,
    128, 225, 144, 31, 82, 67, 58, 140, 109, 167, 128, 227, 140, 35, 94, 243
};

unsigned char data4[] = {
    // Chunk 1
    0x4A, 0x2F, 0x1C, 0x71, 0x5E, 0x84, 0x6B, 0xC2, 0x7F, 0x00, 0x3D, 0x2C, 0x19, 0x71, 0x5A, 0x80,
    // Chunk 2
    0x4A, 0x2F, 0x1C, 0x71, 0x5E, 0x84, 0x6B, 0xC2, 0x7F, 0x00, 0x3D, 0x2C, 0x19, 0x71, 0x5A, 0x97,
    // Chunk 3
    0x4A, 0x2F, 0x1C, 0x71, 0x5E, 0x84, 0x6B, 0xC2, 0x73, 0x0C, 0x41, 0x2C, 0x19, 0x71, 0x5A, 0x52,
    // Chunk 4
    0x4A, 0x2F, 0x1C, 0x71, 0x5E, 0x84, 0x6B, 0xC2, 0x73, 0x0C, 0x41, 0x2C, 0x19, 0x71, 0x5A, 0x2F,
    // Chunk 5
    0x4A, 0x2F, 0x1C, 0x71, 0x5E, 0x84, 0x67, 0xCE, 0x73, 0x0C, 0x41, 0x2C, 0x19, 0x71, 0x5A, 0xB5,
    // Chunk 6
    0x4A, 0x2F, 0x1C, 0x71, 0x5E, 0x84, 0x6B, 0xC2, 0x73, 0x0C, 0x41, 0x2C, 0x19, 0x71, 0x5A, 0x2F,
    // Chunk 7
    0x4A, 0x2F, 0x1C, 0x71, 0x5E, 0x84, 0x6B, 0xC2, 0x73, 0x0C, 0x41, 0x2C, 0x19, 0x71, 0x5A, 0x52,
    // Chunk 8
    0x4A, 0x2F, 0x1C, 0x71, 0x5E, 0x84, 0x6B, 0xC2, 0x7F, 0x00, 0x3D, 0x2C, 0x19, 0x71, 0x5A, 0x80,
};

unsigned char *noteData = (unsigned char*)
  "supermat"
  "superman"
  "subarmak"
  "subarlay"
  "subasort"
;