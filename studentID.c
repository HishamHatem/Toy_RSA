/*
 * Toy RSA Algorithm using Montgomery Multiplication
 * CSE451 Computer & Network Security - Assignment 2
 * 
 * Build: gcc -O3 studentID.c -o studentID
 * 
 * Usage:
 *   ./studentID "g" public_key.txt private_key.txt   (generate keys)
 *   ./studentID "e" public_key.txt plaintext.txt ciphertext.txt   (encrypt)
 *   ./studentID "d" private_key.txt ciphertext.txt plaintext.txt  (decrypt)
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ============================================================================
 * File I/O Functions - Hexadecimal parsing and writing
 * ============================================================================ */

/*
 * Read hexadecimal values from file into array
 * Returns number of values read
 */
int read_hex_file(const char *filename, uint32_t *values, int max_count) {
    FILE *fp = fopen(filename, "r");
    if (!fp) {
        return -1;
    }
    
    int count = 0;
    char hex_str[16];
    
    while (count < max_count && fscanf(fp, "%s", hex_str) == 1) {
        values[count] = (uint32_t)strtoul(hex_str, NULL, 16);
        count++;
    }
    
    fclose(fp);
    return count;
}

/*
 * Write hexadecimal values to file (8-digit uppercase hex)
 */
int write_hex_file(const char *filename, uint32_t *values, int count) {
    FILE *fp = fopen(filename, "w");
    if (!fp) {
        return -1;
    }
    
    for (int i = 0; i < count; i++) {
        if (i > 0) fprintf(fp, " ");
        fprintf(fp, "%08X", values[i]);
    }
    fprintf(fp, "\n");
    
    fclose(fp);
    return 0;
}

/* ============================================================================
 * Mathematical Utilities
 * ============================================================================ */

/*
 * Greatest Common Divisor using Euclidean algorithm
 */
uint32_t gcd(uint32_t a, uint32_t b) {
    while (b != 0) {
        uint32_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}

/*
 * Extended Euclidean Algorithm
 * Finds x, y such that a*x + b*y = gcd(a, b)
 * Returns gcd(a, b)
 */
uint32_t extended_gcd(uint32_t a, uint32_t b, int64_t *x, int64_t *y) {
    if (b == 0) {
        *x = 1;
        *y = 0;
        return a;
    }
    
    int64_t x1, y1;
    uint32_t g = extended_gcd(b, a % b, &x1, &y1);
    
    *x = y1;
    *y = x1 - (int64_t)(a / b) * y1;
    
    return g;
}

/*
 * Modular inverse: a^(-1) mod m
 * Returns 0 if inverse doesn't exist
 */
uint32_t mod_inverse(uint32_t a, uint32_t m) {
    int64_t x, y;
    uint32_t g = extended_gcd(a, m, &x, &y);
    
    if (g != 1) {
        return 0;  /* Inverse doesn't exist */
    }
    
    /* Ensure positive result */
    x = ((x % (int64_t)m) + (int64_t)m) % (int64_t)m;
    return (uint32_t)x;
}

/* ============================================================================
 * Montgomery Multiplication
 * ============================================================================ */

/*
 * Compute N^(-1) mod 2^32 using Newton's method (Hensel lifting)
 * N must be odd for Montgomery to work
 */
uint32_t compute_invN(uint32_t N) {
    uint32_t inv = N;  /* Initial guess: N itself works for odd N */
    
    /* Newton iteration: inv = inv * (2 - N * inv) mod 2^32 */
    /* 5 iterations gives us 32-bit precision */
    for (int i = 0; i < 5; i++) {
        inv = inv * (2 - N * inv);
    }
    
    return inv;  /* Return N^(-1) mod 2^32 */
}

/*
 * Compute R^2 mod N where R = 2^32
 * This is needed to convert numbers into Montgomery space
 */
uint32_t compute_R2modN(uint32_t N) {
    /* R mod N = 2^32 mod N */
    uint64_t R = ((uint64_t)1 << 32) % N;
    
    /* R^2 mod N */
    uint64_t R2 = (R * R) % N;
    
    return (uint32_t)R2;
}

/*
 * Montgomery Reduction (REDC)
 * Computes x * R^(-1) mod N
 * 
 * Formula: REDC(x) = (x - m*N) / R where m = x * N^(-1) mod R
 * Since m*N ≡ x (mod R), the difference is divisible by R
 */
uint32_t montgomery_redc(uint64_t x, uint32_t N, uint32_t invN) {
    uint64_t t1 = x;
    /* m = x * N^(-1) mod R (low 32 bits) */
    uint32_t m = (uint32_t)x * invN;
    /* t2 = m * N */
    uint64_t t2 = (uint64_t)m * N;
    /* result = (t1 - t2) / R using signed arithmetic */
    int64_t diff = (int64_t)t1 - (int64_t)t2;
    int32_t result = (int32_t)(diff >> 32);
    
    /* If result is negative, add N */
    if (result < 0) {
        result += N;
    }
    
    return (uint32_t)result;
}

/*
 * Convert to Montgomery space: a * R mod N
 * Uses REDC(a * R^2 mod N) = a * R mod N
 */
uint32_t to_montgomery(uint32_t a, uint32_t N, uint32_t invN, uint32_t R2modN) {
    return montgomery_redc((uint64_t)a * R2modN, N, invN);
}

/*
 * Convert from Montgomery space back to normal: a * R^(-1) mod N
 * Uses REDC(a) = a * R^(-1) mod N
 */
uint32_t from_montgomery(uint32_t a, uint32_t N, uint32_t invN) {
    return montgomery_redc((uint64_t)a, N, invN);
}

/*
 * Montgomery multiplication: (a * b) mod N in Montgomery space
 * Both a and b should already be in Montgomery space
 */
uint32_t montgomery_mul(uint32_t a, uint32_t b, uint32_t N, uint32_t invN) {
    return montgomery_redc((uint64_t)a * b, N, invN);
}

/* ============================================================================
 * Modular Exponentiation using Montgomery Multiplication
 * ============================================================================ */

/*
 * Compute base^exp mod N using Montgomery multiplication
 * Uses square-and-multiply algorithm
 */
uint32_t montgomery_pow(uint32_t base, uint32_t exp, uint32_t N) {
    if (N == 1) return 0;
    
    /* Precompute Montgomery constants */
    uint32_t invN = compute_invN(N);
    uint32_t R2modN = compute_R2modN(N);
    
    /* Convert base to Montgomery space */
    uint32_t mont_base = to_montgomery(base, N, invN, R2modN);
    
    /* Initialize result as 1 in Montgomery space */
    uint32_t mont_result = to_montgomery(1, N, invN, R2modN);
    
    /* Square-and-multiply algorithm */
    while (exp > 0) {
        if (exp & 1) {
            mont_result = montgomery_mul(mont_result, mont_base, N, invN);
        }
        mont_base = montgomery_mul(mont_base, mont_base, N, invN);
        exp >>= 1;
    }
    
    /* Convert result back from Montgomery space */
    return from_montgomery(mont_result, N, invN);
}

/* ============================================================================
 * RSA Operations
 * ============================================================================ */

/*
 * Simple primality test (trial division)
 * For toy implementation with small primes
 */
int is_prime(uint32_t n) {
    if (n < 2) return 0;
    if (n == 2) return 1;
    if (n % 2 == 0) return 0;
    
    for (uint32_t i = 3; i * i <= n; i += 2) {
        if (n % i == 0) return 0;
    }
    return 1;
}

/*
 * Generate a random prime number in the given range [min, max]
 */
uint32_t random_prime(uint32_t min, uint32_t max) {
    uint32_t candidate;
    do {
        candidate = min + (rand() % (max - min + 1));
        /* Make it odd if even */
        if (candidate % 2 == 0) {
            candidate++;
            if (candidate > max) candidate = min + 1;
        }
    } while (!is_prime(candidate));
    return candidate;
}

/*
 * Generate RSA key pair
 * Uses randomized primes for each call
 */
int rsa_generate_keys(const char *public_key_file, const char *private_key_file) {
    /* Seed random number generator with current time */
    srand((unsigned int)time(NULL));
    
    /* Generate two random 16-bit primes to get a 32-bit modulus */
    /* Range: 256 to 65535 (for reasonable 16-bit primes) */
    uint32_t p = random_prime(256, 65535);
    uint32_t q;
    do {
        q = random_prime(256, 65535);
    } while (q == p);  /* Ensure p and q are different */
    
    uint32_t N = p * q;                    /* N = p * q */
    uint32_t phi = (p - 1) * (q - 1);      /* phi(N) = (p-1) * (q-1) */
    uint32_t e = 257;                      /* Common choice: 0x101 */
    
    /* Ensure gcd(e, phi) = 1 */
    while (gcd(e, phi) != 1) {
        e += 2;
    }
    
    /* Compute private exponent d = e^(-1) mod phi(N) */
    uint32_t d = mod_inverse(e, phi);
    
    if (d == 0) {
        fprintf(stderr, "Error: Could not compute private key\n");
        return -1;
    }
    
    /* Write public key (e, N) */
    uint32_t public_key[2] = {e, N};
    if (write_hex_file(public_key_file, public_key, 2) != 0) {
        fprintf(stderr, "Error: Could not write public key file\n");
        return -1;
    }
    
    /* Write private key (d, N) */
    uint32_t private_key[2] = {d, N};
    if (write_hex_file(private_key_file, private_key, 2) != 0) {
        fprintf(stderr, "Error: Could not write private key file\n");
        return -1;
    }
    
    printf("Key generation successful!\n");
    printf("  p = %u (0x%X)\n", p, p);
    printf("  q = %u (0x%X)\n", q, q);
    printf("  N = %u (0x%X)\n", N, N);
    printf("  phi(N) = %u\n", phi);
    printf("  e = %u (0x%X)\n", e, e);
    printf("  d = %u (0x%X)\n", d, d);
    
    return 0;
}

/*
 * RSA Encryption: C = P^e mod N
 */
int rsa_encrypt(const char *public_key_file, const char *plaintext_file, 
                const char *ciphertext_file) {
    uint32_t key[2];  /* e, N */
    uint32_t plaintext[1];
    
    /* Read public key */
    if (read_hex_file(public_key_file, key, 2) != 2) {
        fprintf(stderr, "Error: Could not read public key file\n");
        return -1;
    }
    
    uint32_t e = key[0];
    uint32_t N = key[1];
    
    /* Read plaintext */
    if (read_hex_file(plaintext_file, plaintext, 1) != 1) {
        fprintf(stderr, "Error: Could not read plaintext file\n");
        return -1;
    }
    
    uint32_t P = plaintext[0];
    
    /* Check that plaintext < N */
    /* Max N = 0x0001E96B */
    if (P >= N) {
        fprintf(stderr, "Error: Plaintext must be less than N\n");
        return -1;
    }
    
    /* Encrypt: C = P^e mod N using Montgomery multiplication */
    uint32_t C = montgomery_pow(P, e, N);
    
    /* Write ciphertext */
    if (write_hex_file(ciphertext_file, &C, 1) != 0) {
        fprintf(stderr, "Error: Could not write ciphertext file\n");
        return -1;
    }
    
    printf("Encryption successful!\n");
    printf("  P = 0x%08X\n", P);
    printf("  C = 0x%08X\n", C);
    
    return 0;
}

/*
 * RSA Decryption: P = C^d mod N
 */
int rsa_decrypt(const char *private_key_file, const char *ciphertext_file,
                const char *plaintext_file) {
    uint32_t key[2];  /* d, N */
    uint32_t ciphertext[1];
    
    /* Read private key */
    if (read_hex_file(private_key_file, key, 2) != 2) {
        fprintf(stderr, "Error: Could not read private key file\n");
        return -1;
    }
    
    uint32_t d = key[0];
    uint32_t N = key[1];
    
    /* Read ciphertext */
    if (read_hex_file(ciphertext_file, ciphertext, 1) != 1) {
        fprintf(stderr, "Error: Could not read ciphertext file\n");
        return -1;
    }
    
    uint32_t C = ciphertext[0];
    
    /* Decrypt: P = C^d mod N using Montgomery multiplication */
    uint32_t P = montgomery_pow(C, d, N);
    
    /* Write plaintext */
    if (write_hex_file(plaintext_file, &P, 1) != 0) {
        fprintf(stderr, "Error: Could not write plaintext file\n");
        return -1;
    }
    
    printf("Decryption successful!\n");
    printf("  C = 0x%08X\n", C);
    printf("  P = 0x%08X\n", P);
    
    return 0;
}

/* ============================================================================
 * Main Function
 * ============================================================================ */

void print_usage(const char *program_name) {
    printf("Usage:\n");
    printf("  %s \"g\" <public_key.txt> <private_key.txt>\n", program_name);
    printf("  %s \"e\" <public_key.txt> <plaintext.txt> <ciphertext.txt>\n", program_name);
    printf("  %s \"d\" <private_key.txt> <ciphertext.txt> <plaintext.txt>\n", program_name);
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        print_usage(argv[0]);
        return 1;
    }
    
    char mode = argv[1][0];
    
    switch (mode) {
        case 'g':
        case 'G':
            /* Key Generation */
            if (argc != 4) {
                fprintf(stderr, "Error: Key generation requires 2 file arguments\n");
                print_usage(argv[0]);
                return 1;
            }
            return rsa_generate_keys(argv[2], argv[3]);
            
        case 'e':
        case 'E':
            /* Encryption */
            if (argc != 5) {
                fprintf(stderr, "Error: Encryption requires 3 file arguments\n");
                print_usage(argv[0]);
                return 1;
            }
            return rsa_encrypt(argv[2], argv[3], argv[4]);
            
        case 'd':
        case 'D':
            /* Decryption */
            if (argc != 5) {
                fprintf(stderr, "Error: Decryption requires 3 file arguments\n");
                print_usage(argv[0]);
                return 1;
            }
            return rsa_decrypt(argv[2], argv[3], argv[4]);
            
        default:
            fprintf(stderr, "Error: Unknown mode '%c'\n", mode);
            print_usage(argv[0]);
            return 1;
    }
    
    return 0;
}
