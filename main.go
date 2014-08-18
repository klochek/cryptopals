package main

import (
	"crypto/aes"
	"crypto/cipher"
	"encoding/base64"
	"bufio"
	"bytes"
	"io"
	"encoding/hex"
	"fmt"
	"math"
	"os"
	"strings"
)

var englishCharFreqMap = map[rune]float64{
	'e': 0.130,
	't': 0.09056,
	'a': 0.08167,
	'o': 0.07507,
	'i': 0.06966,
	'n': 0.06749,
	's': 0.06327,
	'h': 0.06094,
	'r': 0.05987,
	'd': 0.04253,
	'l': 0.04025,
	'c': 0.02782,
	'u': 0.02758,
	'm': 0.02406,
	'w': 0.02360,
	'f': 0.02228,
	'g': 0.02015,
	'y': 0.01974,
	'p': 0.01929,
	'b': 0.01492,
	'v': 0.00978,
	'k': 0.00772,
	'j': 0.00153,
	'x': 0.00150,
	'q': 0.00095,
	'z': 0.00074,
}

func b2hex(b []byte) string {
	return hex.EncodeToString(b)
}

func hex2b(s string) []byte {
	b, _ := hex.DecodeString(s)
	return b
}

func scoreStringAsEnglish(s string) float64 {
	score := 100.0
	charCounts := make(map[rune]int)
	totalChars := 0

	for _, ch := range s {
		// Anything not valid printable ascii means it's crap.
		// A more realistic metric might simply punish this a little,
		// not catastrophically.
		if ch != '\n' && ch != '\r' && (ch < ' ' || ch > '~') {
			return 10000.0
		}

		// tolower
		if ch >= 'A' && ch <= 'Z' {
			ch = ch | 32
		}

		// Don't bother getting the freqs of chars we don't have a table for.
		if ch < 'a' || ch > 'z' {
			continue
		}
		totalChars++
		charCounts[ch]++
	}

	if totalChars > 0 {
		score = 0
	}

	for ch, count := range charCounts {
		dist := math.Abs(englishCharFreqMap[ch] - (float64(count) / float64(totalChars)))
		score += dist * dist
	}

	// Penalize the string if there are lots of uncounted chars.
	score *= float64(len(s) - totalChars)
	return score
}

func fill(b []byte, key []byte) {
	keylen := len(key)
	for i := 0; i < len(b); i++ {
		b[i] = key[i % keylen]
	}
}

func make_fill(bytes []byte, length int) []byte {
	result := make([]byte, length)
	fill(result, bytes)
	return result
}

func hamdist(x, y byte) int {
  dist := 0
  val := x ^ y

  for val > 0 {
    dist++ 
    val &= val - 1;
  }
 
  return dist
}

func hamdist_between(x, y []byte) int {
	dist := 0

	for i, _ := range(x) {
		dist += hamdist(x[i], y[i])
	}
	return dist
}


func xorBuffers(a, b []byte) []byte {
	res := make([]byte, len(a))
	for i := 0; i < len(a); i++ {
		res[i] = a[i] ^ b[i]
	}
	return res
}

func guess_keysize(data []byte, min, max int) int {
	bestGuess :=  1000000
	nBest := 100000.0

	for guess := min; guess < max; guess++ {
		blockPairsToCheck := int(math.Min(64, float64(len(data) / guess))) & 0xfffffffe
		dist := 0
		for i := 0; i < blockPairsToCheck; i+=2 {
			s := i * guess
			m := (i + 1) * guess
			e := (i + 2) * guess
			dist += hamdist_between(data[s:m], data[m:e])
		}
		ndist := float64(dist) / float64(guess) * (float64(blockPairsToCheck) / 2.0)
		if ndist < nBest {
			nBest = ndist
			bestGuess = guess
		}
	}
	return bestGuess
}

func transpose_by_block(data []byte, block_size int) [][]byte {
	bytesPerBlock := (len(data) / block_size) + 1
	result := make([][]byte, block_size)

	for i, _ := range(result) {
		result[i] = make([]byte, bytesPerBlock)
	}

	for i, _ := range(data) {
		result[i % block_size][i / block_size] = data[i]
	}

	return result
}

func retrieve_key_byte(data []byte) byte {
	bestScore := 1000000.0
	var bestVal byte = 0
	tempB := make([]byte, len(data))
	for i := 0; i < 256; i++ {
		fill(tempB, []byte{byte(i)})
		r := xorBuffers(data, tempB)

		newScore := scoreStringAsEnglish(string(r))

		if newScore < bestScore {
			bestScore = newScore
			bestVal = byte(i)
		}
	}
	return bestVal
}

func retrieve_key(cyphertext []byte, key_len int) []byte {
	transposed_data := transpose_by_block(cyphertext, key_len)

	key := make([]byte, key_len)
	for i, d := range(transposed_data) {
		key[i] = retrieve_key_byte(d)
	}
	return key
}

func readBase64File(name string) []byte {
	f, err := os.Open(name)
	defer f.Close()
	if err != nil {
		panic("Couldn't find file!")
	}

	var buf bytes.Buffer
	scanner := bufio.NewScanner(f)

	for scanner.Scan() {
		t,err := base64.StdEncoding.DecodeString(scanner.Text())
		if err != nil {
			panic(fmt.Sprintf("Error reading file line: %s", err.Error()))
		}
		buf.Write(t)
	}
	return buf.Bytes()	
}

type ECBReader struct {
	data io.Reader
	block cipher.Block
}

func (e *ECBReader) Read(p []byte) (n int, err error) {
	n, err = e.data.Read(p)

	blocks := n / e.block.BlockSize()
	for i := 0; i < blocks; i++ {
		start := i * e.block.BlockSize()
		end := (i + 1) * e.block.BlockSize()
		e.block.Decrypt(p[start:end], p[start:end])
	}
	return
}


func NewECBDecrypter(block cipher.Block, ciphertext io.Reader) ECBReader {
	return ECBReader{data: ciphertext, block: block}
}

func pkcs_7_pad(block []byte, desired_length int) []byte {
	result := block[:]
	diff := desired_length - len(block)
	padding := make_fill([]byte{byte(diff)}, diff)
	return append(result, padding...)
}

const (
	Encrypt = iota
	Decrypt
)

type CBCReader struct {
	data io.Reader
	block cipher.Block
	mode int
}

func (r *CBCReader) encrypt(p []byte) (int, error) {
	maxblocks := len(p) / r.block.BlockSize()

	if maxblocks < 1 {
		panic("need moar bytes")
	}

	buff := make([]byte, maxblocks * r.block.BlockSize())

	n, err := r.data.Read(buff)

	numBlocks := n / r.block.BlockSize()
	residual := n % r.block.BlockSize()
	if residual > 0 {
		numBlocks++
	}

	// TODO initialization vector
	prevBlock := make([]byte, r.block.BlockSize())

	i := 0
	for ;i < numBlocks - 1; i++ {
		start := i * r.block.BlockSize()
		end := (i + 1) * r.block.BlockSize()
		r.block.Encrypt(p[start:end], xorBuffers(buff[start:end], prevBlock))

		prevBlock = p[start:end]			
	}

	start := i * r.block.BlockSize()
	lastBlock := pkcs_7_pad(buff[start:start + residual], r.block.BlockSize())
	r.block.Encrypt(p[start:], xorBuffers(lastBlock, prevBlock))

	return n + residual, err
}

func (r *CBCReader) decrypt(p []byte) (n int, err error) {
	maxblocks := len(p) / r.block.BlockSize()
	buff := make([]byte, maxblocks * r.block.BlockSize())

	n, err = r.data.Read(buff)

	if n % r.block.BlockSize() != 0 {
		panic("Bad block size")
	}

	numBlocks := n / r.block.BlockSize()

	// TODO initialization vector
	prevBlock := make([]byte, r.block.BlockSize())

	for i := 0; i < numBlocks; i++ {
		start := i * r.block.BlockSize()
		end := (i + 1) * r.block.BlockSize()

		r.block.Decrypt(p[start:end], buff[start:end])
		copy(p[start:end], xorBuffers(p[start:end], prevBlock))
		prevBlock = buff[start:end]
	}
	return
}


func (r *CBCReader) Read(p []byte) (n int, err error) {
	if r.mode == Encrypt {
		return r.encrypt(p)
	}
	return	r.decrypt(p)
}

func NewCBCEncrypter(key []byte, data io.Reader) CBCReader {
	block, _ := aes.NewCipher(key)
	return CBCReader{data: data, mode: Encrypt, block: block}
}

func NewCBCDecrypter(key []byte, data io.Reader) CBCReader {
	block, _ := aes.NewCipher(key)
	return CBCReader{data: data, mode: Decrypt, block: block}
}


func c10() {
	ciphertext := bytes.NewBuffer(readBase64File("10.txt"))

	reader := NewCBCDecrypter([]byte("YELLOW SUBMARINE"), ciphertext)
	dst := make([]byte, 16 * 10000)

	reader.Read(dst)
	
	fmt.Println(string(dst))
}

func c9() {
	fmt.Println((pkcs_7_pad([]byte("YELLOW SUBMARINE"), 20)))
}

// Seriously?
func c8() {
	f, _ := os.Open("8.txt")
	defer f.Close()

	scanner := bufio.NewScanner(f)
	lineNo := 0
	for scanner.Scan() {
		inp := hex2b(strings.TrimSpace(scanner.Text()))
		all := make([][]byte, 10)

		for j := 0; j < 10; j++ {
			s := j * 16
			e := (j + 1) * 16
			all[j] = inp[s:e]
		}

		for i := 0; i < 10; i++ {
			for j := i + 1; j < 10; j++ {
				same := true
				for k := 0; k < 16; k++ {
					if all[j][k] != all[i][k] {
						same = false
						break
					}
				}
				if same {
					fmt.Println(lineNo)
				}
			}
		}
		lineNo++
	}
}

func c7() {
	aesCipher,_ := aes.NewCipher([]byte("YELLOW SUBMARINE"))
	ciphertext := bytes.NewBuffer(readBase64File("7.txt"))

	reader := NewECBDecrypter(aesCipher, ciphertext)
	dst := make([]byte, aesCipher.BlockSize() * 10000)

	reader.Read(dst)
	
	fmt.Println(string(dst))
}

func c6() {
	cyphertext := readBase64File("6.txt")

	// Naive.  A better approach would be to return ALL keys in ranked order.
	// Also, some debug switches that could allow a programmer to explore
	// the key-space would be nice.
	key_len_guess := guess_keysize(cyphertext, 2, 40)

	fmt.Printf("[Guessed %d key length.]\n", key_len_guess)

	key := retrieve_key(cyphertext, key_len_guess)

	fmt.Printf("[I think the key is %q]\n", key)

	keybuff := make_fill(key, len(cyphertext))

	fmt.Println("[Decrypted text:]")
	fmt.Println(string(xorBuffers(cyphertext, keybuff)))
}

func c5() {
	s := "Burning 'em, if you ain't quick and nimble\nI go crazy when I hear a cymbal"
	r := make([]byte, len(s))
	fill(r, []byte("ICE"))

	c := xorBuffers([]byte(s), r)

	fmt.Println(b2hex(c))
}


func c4() {

	f, _ := os.Open("4.txt")
	defer f.Close()

	scanner := bufio.NewScanner(f)
	var bestVal []byte
	i := 0
	bestScore := 10000.0
	for scanner.Scan() {
		inp := hex2b(strings.TrimSpace(scanner.Text()))

		tempB := make([]byte, len(inp))
		for i := 0; i < 256; i++ {
			fill(tempB, []byte{byte(i)})
			r := xorBuffers(inp, tempB)

			newScore := scoreStringAsEnglish(string(r))

			if newScore < bestScore {
				bestScore = newScore
				bestVal = r
			}
		}
		i++
	}
	fmt.Printf("%f: --%s--\n",bestScore, string(bestVal))
}
