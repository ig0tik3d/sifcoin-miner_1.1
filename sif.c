#include "cpuminer-config.h"
#include "miner.h"

//#define QUARK_AES 1
//#define QUARK_VPERM 1
//#define QUARK_ITR 1

#include <string.h>
#include <stdint.h>

#include "blake.c"
#include "bmw.c"
#include "keccak.c"
#include "skein.c"
#include "jh_sse2_opt64.h"
//#include "groestl.c"

#if 1
#include "grso.c"
#ifndef PROFILERUN
#include "grso-asm.c"
#endif
#else
#include "grss_api.h"
#endif

/*define data alignment for different C compilers*/
#if defined(__GNUC__)
      #define DATA_ALIGN16(x) x __attribute__ ((aligned(16)))
#else
      #define DATA_ALIGN16(x) __declspec(align(16)) x
#endif

//#define SPEEDRUN

inline void sifhash(void *state, const void *input)
{
    /* shared  temp space */
    /* hash is really just 64bytes but it used to hold both hash and final round constants passed 64 */
    DATA_ALIGN16(unsigned char hashbuf[128]);
    DATA_ALIGN16(size_t hashptr);
    DATA_ALIGN16(sph_u64 hashctA);
    DATA_ALIGN16(sph_u64 hashctB);

    //sph_keccak512_context    ctx_keccak;
    //sph_groestl512_context ctx_grs;
    grsoState sts_grs;
    //grssState sts_grs;
    
//#ifdef SPEEDRUN
    /* just run one of each */
    int speedrun[] = {0, 1, 3, 4, 6, 7 };
//#endif

    int i;

    DATA_ALIGN16(unsigned char hash[128]);
    /* proably not needed */
    memset(hash, 0, 128);
    DECL_BLK;
    BLK_I;
    BLK_W;
//#ifndef SPEEDRUN
    /* this layout is so each "function" inlined just once */
    /* i is not special rounds */
    /* i+16 is  special rounds */
 //   for(i=0; i<9; i++) {
//#else
    for (i=0;i<6;i++) {
//#endif
    /* blake is split between 64byte hashes and the 80byte initial block */
    //DECL_BLK;
//#ifndef SPEEDRUN
//    switch (i+(16*((hash[0] & (uint32_t)(8)) == (uint32_t)(0))))
//#else
    switch (speedrun[i])
//#endif
    {
        case 5 :
            BLK_I;
            BLK_U;
        case 0:
        case 16: 
            BLK_C;
            break;
        case 1:
        case 17:
        case 21: do { 
            DECL_BMW;
            BMW_I;
            BMW_U;
/* bmw compress uses some defines */
/* i havent gotten around to rewriting these */
#define M(x)    sph_dec64le_aligned(data + 8 * (x))
#define H(x)    (h[x])
#define dH(x)   (dh[x])
            BMW_C;
#undef M
#undef H
#undef dH
            } while(0); continue;;
        case 2:
#ifdef CHEAT
                 /* blake and bmw are almost free
                  * if luck means that groestl will now be run twice
                  * give up and try another nonce */
                 return;
#endif
        case 19:
        case 3: do {
            GRS_I;
            GRS_U;
            GRS_C;
            //grsoInit(&sts_grs);
            //grsoUpdateq(&sts_grs, (char*)hash);
            //grsoFinal(&sts_grs, (char*)hash);
            //grssInit(&sts_grs,512);
            //grssUpdate(&sts_grs, (char*)hash,128*8*4);
            //grssFinal(&sts_grs, (char*)hash);
            } while(0); continue;
        case 4:
        case 20:
        case 24: do {
            DECL_JH;
            /* JH ended up being really short */
            JH_H;
            } while(0); continue;
        case 6:
        case 22:
        case 8: do {
            DECL_KEC;
            KEC_I;
            KEC_U;
            KEC_C;
            } while(0); continue;
        case 18:
        case 7:
        case 23: do {
            DECL_SKN;
            SKN_I;
            SKN_U;
            SKN_C; /* is a magintue faster than others, done */
            } while(0); continue;
        default:
            /* bad things happend, i counted to potato */
            abort();
    }
    /* only blake shouuld get here without continue */
    /* blake finishs from top split */
    //BLK_C;
 }
 asm volatile ("emms");
    memcpy(state, hash, 32);
}

int scanhash_sif(int thr_id, uint32_t *pdata, const uint32_t *ptarget,
	uint32_t max_nonce, unsigned long *hashes_done)
{
	       uint32_t n = pdata[19] - 1;
        const uint32_t first_nonce = pdata[19];
        const uint32_t Htarg = ptarget[7];

        uint32_t hash64[8] __attribute__((aligned(32)));
        uint32_t endiandata[32];
        
        //char testdata[] = {"\x70\x00\x00\x00\x5d\x38\x5b\xa1\x14\xd0\x79\x97\x0b\x29\xa9\x41\x8f\xd0\x54\x9e\x7d\x68\xa9\x5c\x7f\x16\x86\x21\xa3\x14\x20\x10\x00\x00\x00\x00\x57\x85\x86\xd1\x49\xfd\x07\xb2\x2f\x3a\x8a\x34\x7c\x51\x6d\xe7\x05\x2f\x03\x4d\x2b\x76\xff\x68\xe0\xd6\xec\xff\x9b\x77\xa4\x54\x89\xe3\xfd\x51\x17\x32\x01\x1d\xf0\x73\x10\x00"};
        
        //we need bigendian data...
        //lessons learned: do NOT endianchange directly in pdata, this will all proof-of-works be considered as stale from minerd....
        int kk=0;
        for (; kk < 32; kk++)
        {
                be32enc(&endiandata[kk], ((uint32_t*)pdata)[kk]);
        };

//        if (opt_debug)
//        {
//                applog(LOG_DEBUG, "Thr: %02d, firstN: %08x, maxN: %08x, ToDo: %d", thr_id, first_nonce, max_nonce, max_nonce-first_nonce);
//        }
        
        /* I'm to lazy to put the loop in an inline function... so dirty copy'n'paste.... */
        /* i know that i could set a variable, but i don't know how the compiler will optimize it, not that then the cpu needs to load the value *everytime* in a register */
        if (ptarget[7]==0) {
                do {
                        pdata[19] = ++n;
                        be32enc(&endiandata[19], n);
                        sifhash(hash64, &endiandata);
                        if (((hash64[7]&0xFFFFFFFF)==0) &&
                                        fulltest(hash64, ptarget)) {
                                *hashes_done = n - first_nonce + 1;
                                return true;
                        }
                } while (n < max_nonce && !work_restart[thr_id].restart);        
        }
        else if (ptarget[7]<=0xF)
        {
                do {
                        pdata[19] = ++n;
                        be32enc(&endiandata[19], n);
                        sifhash(hash64, &endiandata);
                        if (((hash64[7]&0xFFFFFFF0)==0) &&
                                        fulltest(hash64, ptarget)) {
                                *hashes_done = n - first_nonce + 1;
                                return true;
                        }
                } while (n < max_nonce && !work_restart[thr_id].restart);        
        }
        else if (ptarget[7]<=0xFF)
        {
                do {
                        pdata[19] = ++n;
                        be32enc(&endiandata[19], n);
                        sifhash(hash64, &endiandata);
                        if (((hash64[7]&0xFFFFFF00)==0) &&
                                        fulltest(hash64, ptarget)) {
                                *hashes_done = n - first_nonce + 1;
                                return true;
                        }
                } while (n < max_nonce && !work_restart[thr_id].restart);        
        }
        else if (ptarget[7]<=0xFFF)
        {
                do {
                        pdata[19] = ++n;
                        be32enc(&endiandata[19], n);
                        sifhash(hash64, &endiandata);
                        if (((hash64[7]&0xFFFFF000)==0) &&
                                        fulltest(hash64, ptarget)) {
                                *hashes_done = n - first_nonce + 1;
                                return true;
                        }
                } while (n < max_nonce && !work_restart[thr_id].restart);        

        }
        else if (ptarget[7]<=0xFFFF)
        {
                do {
                        pdata[19] = ++n;
                        be32enc(&endiandata[19], n);
                        sifhash(hash64, &endiandata);
                        if (((hash64[7]&0xFFFF0000)==0) &&
                                        fulltest(hash64, ptarget)) {
                                *hashes_done = n - first_nonce + 1;
                                return true;
                        }
                } while (n < max_nonce && !work_restart[thr_id].restart);        

        }
        else
        {
                do {
                        pdata[19] = ++n;
                        be32enc(&endiandata[19], n);
                        sifhash(hash64, &endiandata);
                        if (fulltest(hash64, ptarget)) {
                                *hashes_done = n - first_nonce + 1;
                                return true;
                        }
                } while (n < max_nonce && !work_restart[thr_id].restart);        
        }
        
        
        *hashes_done = n - first_nonce + 1;
        pdata[19] = n;
        return 0;
}
