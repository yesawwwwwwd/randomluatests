local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local HttpService = game:GetService("HttpService")
local Lighting = game:GetService("Lighting")
local CoreGui = game:GetService("CoreGui")
local LocalPlayer = Players.LocalPlayer
local PlayerGui = LocalPlayer:WaitForChild("PlayerGui")

local existingGui = PlayerGui:FindFirstChild("PasswordStudioMerged")
if existingGui then existingGui:Destroy() end

--------------------------------------------------------------------------------
-- UTILITY & MATH
--------------------------------------------------------------------------------

local bit = bit32 -- Luau native bit32
local function clamp(a,b,c) if a < b then return b elseif a > c then return c else return a end end
local function round(n, d) d = d or 0 local p = 10^d return math.floor(n*p + 0.5)/p end
local function fmt_scientific(n) if n == math.huge then return "∞" end if not n or n ~= n then return "0" end if n == 0 then return "0" end local e = math.floor(math.log10(math.abs(n))) local m = n / (10^e) return string.format("%.3f×10^%d", m, e) end
local function format_commas(n) if not n or n ~= n then return "0" end if n == math.huge then return "∞" end local s = tostring(math.floor(n + 0.5)) local sign = s:sub(1,1) == "-" and "-" or "" if sign == "-" then s = s:sub(2) end local res = s:reverse():gsub("(%d%d%d)","%1,"):reverse() if res:sub(1,1) == "," then res = res:sub(2) end return sign..res end
local function safe_pow(a,b) local res = a^b if res == math.huge or res ~= res then return math.huge end return res end
local function try_set_clipboard(text) local ok = pcall(function() setclipboard(text) end) return ok end
local function to_hex(str) return (str:gsub('.', function (c) return string.format('%02x', string.byte(c)) end)) end

-- Helper Bitwise (Dari Kode 1, untuk SHA dan ChaCha)
local function to_bytes(n, len)
    local t = {}
    for i=1,len do t[i] = bit.band(bit.rshift(n, (i-1)*8), 0xFF) end
    return t
end
local function from_bytes(t)
    local n = 0
    for i=#t,1,-1 do n = bit.bor(bit.lshift(n, 8), t[i]) end
    return n
end
local function hex_str(bytes)
    local s = {}
    for i=1,#bytes do s[i] = string.format("%02x", bytes[i]) end
    return table.concat(s)
end

--------------------------------------------------------------------------------
-- CRYPTOGRAPHIC CORE (REAL IMPLEMENTATIONS - DARI KODE 1)
--------------------------------------------------------------------------------

local Crypto = {}

-- Helper: Rotates
local function rotl(v, c) return bit.bor(bit.lshift(v,c), bit.rshift(v,32-c)) end
local function rrot(n,b) return bit.bor(bit.rshift(n,b), bit.lshift(n,32-b)) end

-- [[ PRNG: LCG ]]
Crypto.LCG = {}
Crypto.LCG.__index = Crypto.LCG
function Crypto.LCG.new(seed)
    local self = setmetatable({}, Crypto.LCG)
    self.state = seed
    return self
end
function Crypto.LCG:next()
    -- Standard glibc params
    self.state = (1103515245 * self.state + 12345) % 2147483648
    return self.state / 2147483648
end

-- [[ PRNG: Xorshift32 ]]
Crypto.Xorshift = {}
Crypto.Xorshift.__index = Crypto.Xorshift
function Crypto.Xorshift.new(seed)
    local self = setmetatable({}, Crypto.Xorshift)
    self.state = (seed == 0) and 0xDEADBEEF or seed
    return self
end
function Crypto.Xorshift:next()
    local x = self.state
    x = bit.bxor(x, bit.lshift(x, 13))
    x = bit.bxor(x, bit.rshift(x, 17))
    x = bit.bxor(x, bit.lshift(x, 5))
    self.state = x
    return bit.band(x, 0xFFFFFFFF) / 4294967296
end

-- [[ PRNG: Mersenne Twister 19937 ]]
Crypto.MT19937 = {}
Crypto.MT19937.__index = Crypto.MT19937
function Crypto.MT19937.new(seed)
    local self = setmetatable({}, Crypto.MT19937)
    self.mt = {}
    self.index = 625
    self.mt[1] = seed
    for i=2,624 do
        local prev = self.mt[i-1]
        self.mt[i] = bit.band(0xFFFFFFFF, 1812433253 * bit.bxor(prev, bit.rshift(prev, 30)) + i - 1)
    end
    return self
end
function Crypto.MT19937:twist()
    for i=1,624 do
        local y = bit.band(0x80000000, self.mt[i]) + bit.band(0x7FFFFFFF, self.mt[(i%624)+1])
        self.mt[i] = bit.bxor(self.mt[( (i + 396) % 624 ) + 1], bit.rshift(y,1))
        if y % 2 ~= 0 then self.mt[i] = bit.bxor(self.mt[i], 0x9908B0DF) end
    end
    self.index = 1
end
function Crypto.MT19937:next()
    if self.index >= 625 then self:twist() end
    local y = self.mt[self.index]
    y = bit.bxor(y, bit.rshift(y, 11))
    y = bit.bxor(y, bit.band(bit.lshift(y, 7), 0x9D2C5680))
    y = bit.bxor(y, bit.band(bit.lshift(y, 15), 0xEFC60000))
    y = bit.bxor(y, bit.rshift(y, 18))
    self.index = self.index + 1
    return bit.band(y, 0xFFFFFFFF) / 4294967296
end

-- [[ CSPRNG: ChaCha20 Implementation ]]
Crypto.ChaCha = {}
local function qr(a,b,c,d)
    a=bit.band(a+b,0xFFFFFFFF); d=bit.bxor(d,a); d=rotl(d,16)
    c=bit.band(c+d,0xFFFFFFFF); b=bit.bxor(b,c); b=rotl(b,12)
    a=bit.band(a+b,0xFFFFFFFF); d=bit.bxor(d,a); d=rotl(d,8)
    c=bit.band(c+d,0xFFFFFFFF); b=bit.bxor(b,c); b=rotl(b,7)
    return a,b,c,d
end

function Crypto.ChaCha.block(key, nonce, counter, rounds)
    -- Initial State
    local s = {
        0x61707865, 0x3320646e, 0x796b2d32, 0x6b206574,
        key[1], key[2], key[3], key[4],
        key[5], key[6], key[7], key[8],
        counter, nonce[1], nonce[2], nonce[3]
    }
    local x = {unpack(s)}
    -- Rounds
    for i=1,rounds,2 do
        x[1], x[5], x[9],  x[13] = qr(x[1], x[5], x[9],  x[13])
        x[2], x[6], x[10], x[14] = qr(x[2], x[6], x[10], x[14])
        x[3], x[7], x[11], x[15] = qr(x[3], x[7], x[11], x[15])
        x[4], x[8], x[12], x[16] = qr(x[4], x[8], x[12], x[16])
        x[1], x[6], x[11], x[16] = qr(x[1], x[6], x[11], x[16])
        x[2], x[7], x[12], x[13] = qr(x[2], x[7], x[12], x[13])
        x[3], x[8], x[9],  x[14] = qr(x[3], x[8], x[9],  x[14])
        x[4], x[5], x[10], x[15] = qr(x[4], x[5], x[10], x[15])
    end
    -- Add state to working state
    local out = {}
    for i=1,16 do 
        local v = bit.band(x[i] + s[i], 0xFFFFFFFF)
        -- Serialize Little Endian
        table.insert(out, bit.band(v, 0xFF))
        table.insert(out, bit.band(bit.rshift(v,8), 0xFF))
        table.insert(out, bit.band(bit.rshift(v,16), 0xFF))
        table.insert(out, bit.band(bit.rshift(v,24), 0xFF))
    end
    return out
end

-- [[ CSPRNG: SHA-256 Implementation (Real) ]]
Crypto.SHA256 = {}
local K = {
   0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
}

function Crypto.SHA256.digest_seed_counter(seedNum, counter)
    -- Pre-processing: We create a virtual message "Seed(4bytes)||Counter(4bytes)"
    local h = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19}
    
    local w = {}
    -- Block 1: Seed, Counter, Padding
    w[1] = seedNum
    w[2] = counter
    w[3] = 0x80000000 -- Padding start '1' bit
    for i=4,15 do w[i] = 0 end
    w[16] = 64 -- Length in bits (seed+counter = 8 bytes = 64 bits)
    
    -- Schedule
    for i=17,64 do
        local s0 = bit.bxor(rrot(w[i-15],7), rrot(w[i-15],18), bit.rshift(w[i-15],3))
        local s1 = bit.bxor(rrot(w[i-2],17), rrot(w[i-2],19), bit.rshift(w[i-2],10))
        w[i] = bit.band(w[i-16] + s0 + w[i-7] + s1, 0xFFFFFFFF)
    end
    
    local a,b,c,d,e,f,g,h_ = unpack(h)
    for i=1,64 do
        local S1 = bit.bxor(rrot(e,6), rrot(e,11), rrot(e,25))
        local ch = bit.bxor(bit.band(e,f), bit.band(bit.bnot(e),g))
        local temp1 = bit.band(h_ + S1 + ch + K[i] + w[i], 0xFFFFFFFF)
        local S0 = bit.bxor(rrot(a,2), rrot(a,13), rrot(a,22))
        local maj = bit.bxor(bit.band(a,b), bit.band(a,c), bit.band(b,c))
        local temp2 = bit.band(S0 + maj, 0xFFFFFFFF)
        
        h_ = g
        g = f
        f = e
        e = bit.band(d + temp1, 0xFFFFFFFF)
        d = c
        c = b
        b = a
        a = bit.band(temp1 + temp2, 0xFFFFFFFF)
    end
    
    h[1] = bit.band(h[1]+a,0xFFFFFFFF)
    h[2] = bit.band(h[2]+b,0xFFFFFFFF)
    h[3] = bit.band(h[3]+c,0xFFFFFFFF)
    h[4] = bit.band(h[4]+d,0xFFFFFFFF)
    h[5] = bit.band(h[5]+e,0xFFFFFFFF)
    h[6] = bit.band(h[6]+f,0xFFFFFFFF)
    h[7] = bit.band(h[7]+g,0xFFFFFFFF)
    h[8] = bit.band(h[8]+h_,0xFFFFFFFF)
    
    local out = {}
    for i=1,8 do
        local v = h[i]
        table.insert(out, bit.band(bit.rshift(v,24), 0xFF))
        table.insert(out, bit.band(bit.rshift(v,16), 0xFF))
        table.insert(out, bit.band(bit.rshift(v,8), 0xFF))
        table.insert(out, bit.band(v, 0xFF))
    end
    return out
end

-- [[ GENERATOR WRAPPER (DARI KODE 1) ]]
local function GenerateRNG(mode, subMode, seed, length)
    local result = {}
    local sNum = 0
    -- Simple seed hash for numeric seed needed by PRNGs
    for i=1,#seed do sNum = bit.band(sNum + string.byte(seed,i) * i, 0xFFFFFFFF) end
    if sNum == 0 then sNum = 123456789 end

    if mode == "PRNG" then
        local rng
        if subMode == "LCG" then rng = Crypto.LCG.new(sNum)
        elseif subMode == "Mersenne Twister" then rng = Crypto.MT19937.new(sNum)
        elseif subMode == "Xorshift" then rng = Crypto.Xorshift.new(sNum)
        elseif subMode == "math.random" then math.randomseed(sNum % 10000) rng = {next=function() return math.random() end}
        elseif subMode == "Random.new" then local r = Random.new(sNum) rng = {next=function() return r:NextNumber() end}
        end
        
        if rng then
            for i=1,length do
                local val = rng:next()
                table.insert(result, string.format("%02x", math.floor(val * 255)))
            end
        end
        
    elseif mode == "CSPRNG" then
        -- ChaCha Setup
        if subMode:find("ChaCha") then
            local rounds = 20
            if subMode:find("8") then rounds = 8 elseif subMode:find("12") then rounds = 12 end
            
            -- Key setup (derive from seed)
            local key = {sNum, bit.bxor(sNum, 0xAAAAAAAA), bit.bxor(sNum, 0x55555555), sNum+1, sNum+2, sNum+3, sNum+4, sNum+5}
            local nonce = {0,0,0}
            
            local bytes_needed = length
            local counter = 0
            while #result < bytes_needed * 2 do
                counter = counter + 1
                local block = Crypto.ChaCha.block(key, nonce, counter, rounds)
                for _, b in ipairs(block) do
                    if #result < bytes_needed * 2 then
                        table.insert(result, string.format("%02x", b))
                    end
                end
            end
            
            if subMode:find("Poly1305") then table.insert(result, "-[MAC_TAG]") end
            if subMode:find("AEAD") then table.insert(result, "-[AUTH]") end

        -- SHA Setup (Hash_DRBG style)
        elseif subMode:find("Sha") then
            local counter = 0
            while #result < length * 2 do
                counter = counter + 1
                local block = Crypto.SHA256.digest_seed_counter(sNum, counter)
                -- If it's SHA-512 requested, we simulate the larger block by hashing the hash
                if subMode:find("512") or subMode:find("384") then
                    local ext = Crypto.SHA256.digest_seed_counter(sNum + 1, counter)
                    for _,b in ipairs(ext) do table.insert(block, b) end
                end
                
                for _, b in ipairs(block) do
                    if #result < length * 2 then
                        table.insert(result, string.format("%02x", b))
                    end
                end
            end
        end
    end
    return table.concat(result)
end

--------------------------------------------------------------------------------
-- DATA & CONFIG (DARI KODE 2)
--------------------------------------------------------------------------------

local keyboardRows = {
	"1234567890-=", "qwertyuiop[]\\", "asdfghjkl;'", "zxcvbnm,./", "0987654321", "poiuytrewq"
}

local commonPasswords = {
	"password","123456","12345678","qwerty","abc123","letmein","monkey","dragon",
	"admin","welcome","iloveyou","trustno1","sunshine","master","hello","freedom"
}

local wordbank = {
	"alpha","bravo","charlie","delta","echo","foxtrot","golf","hotel","india","joker",
	"kilo","lima","mango","nectar","orbit","pixel","quantum","radar","sigma","tango",
	"ultra","vivid","whiskey","xenon","yonder","zephyr","nebula","aster","lumen","nova"
}

local themes = {
	["Dark Cyber"] = {
		bg = Color3.fromRGB(15,18,28),
		panel = Color3.fromRGB(24,28,40),
		accent = Color3.fromRGB(88, 198, 255),
		text = Color3.fromRGB(235,235,240)
	},
	["Vaporwave"] = {
		bg = Color3.fromRGB(18,13,36),
		panel = Color3.fromRGB(36,22,60),
		accent = Color3.fromRGB(255,105,180),
		text = Color3.fromRGB(250,240,255)
	},
	["Hacker Green"] = {
		bg = Color3.fromRGB(5,10,5),
		panel = Color3.fromRGB(10,20,10),
		accent = Color3.fromRGB(90,255,110),
		text = Color3.fromRGB(200,255,200)
	},
	["Gold Premium"] = {
		bg = Color3.fromRGB(20,16,12),
		panel = Color3.fromRGB(36,30,24),
		accent = Color3.fromRGB(255,195,55),
		text = Color3.fromRGB(245,240,235)
	}
}

local modes = {
	{
		key = "GAMING",
		label = "Gaming PC (High-end consumer)",
		attack_profiles = {
			{name="GPU BruteForce (single flagship GPU)", guesses_per_second=1.0e11},
			{name="GPU BruteForce (SLI/CF cluster 4x)", guesses_per_second=4.0e11},
			{name="CPU Multithread (single modern HEDT)", guesses_per_second=1.2e10},
			{name="Hybrid GPU-CPU (local optimized)", guesses_per_second=1.5e11}
		},
		spec = {cpu="High-end consumer CPU", gpu="Flagship GPU", ram="128 GB DDR5"},
		statuses = {
			"Trivial (seconds)","Very Weak (minutes)","Weak (hours)","Poor (days)","Below Average (weeks)",
			"Average (months)","Strong-ish (years)","Very Strong (decades)","Extremely Strong (centuries)",
			"Near-Uncrackable (millennia)","Quantum-Safe Level I (beyond centuries)","Military-Grade",
			"Consumer-Uncrackable","Cracked in Simulation","Resistant","State-of-the-art Required",
			"Massive Compute Needed","Practically Impossible","Archive-Safe","Legendary"
		}
	},
	{
		key = "SUPERC",
		label = "El Capitan (World's fastest supercomputer)",
		attack_profiles = {
			{name="Single El Capitan Peak-style", guesses_per_second=1.8e18 * 0.2},
			{name="El Capitan full distributed optimized", guesses_per_second=1.8e18 * 0.6},
			{name="Global HPC farm (10x El Capitan)", guesses_per_second=1.8e18 * 6.0}
		},
		spec = {name="El Capitan", model="HPE Cray EX255a", rmax="1.809 exaFLOPS"},
		statuses = {
			"Trivial for HPC","Crackable for motivated adversary","Practical within years","Practical within decades",
			"Practical within centuries","Extended-time attackable","Massive Parallel Required","Specialized Attack Needed",
			"At Risk - Weak","At Risk - Moderate","At Risk - Low","Unlikely in Lifetime","Unlikely for Centuries",
			"Quantum Threat Level I","Supercomputer-Resilient","Long-Term Safe","Archive-Safe","Practicality Barrier",
			"Effectively Secure","Epoch-Proof"
		}
	},
	{
		key = "QUANTUM",
		label = "D-Wave Advantage (Quantum)",
		attack_profiles = {
			{name="Quantum Annealing (D-Wave class)", guesses_per_second=5.0e13},
			{name="Universal Quantum (Grover-limited)", guesses_per_second=1.0e20},
			{name="Hybrid Quantum-Accelerator cluster", guesses_per_second=5.0e20}
		},
		spec = {name="D-Wave Advantage / Advantage2", qubits="5,000+ physical qubits"},
		statuses = {
			"Immediate (sub-ms)","Extremely Fast (ms)","Very Fast (ms - sub-s)","Fast (seconds)","High-Speed (seconds - minutes)",
			"Accelerated (minutes)","Quantum-Assisted (hours)","Hybrid Threat (hours-days)","Significant Risk","Critical Risk",
			"Severe Risk","Short-Term Vulnerable","Medium-Term Vulnerable","Hard to Crack","Rarely Crackable","Unlikely Crackable",
			"Practically Impossible","Breakthrough-Proof","Post-Quantum Secure","Quantum-Resilient"
		}
	}
}

local attackModes = {
	{label="Gaming PC", profiles={{name="GPU (flagship)",gps=1e11},{name="4x GPU cluster",gps=4e11},{name="CPU HEDT",gps=1.2e10},{name="Hybrid GPU-CPU",gps=1.5e11}}},
	{label="El Capitan HPC", profiles={{name="El Capitan peak",gps=1.8e18*0.2},{name="El Capitan optimized",gps=1.8e18*0.6},{name="Global HPC farm",gps=1.8e18*6.0}}},
	{label="Quantum Model", profiles={{name="Quantum annealer",gps=5e13},{name="Grover-like universal",gps=1e20},{name="Hybrid Quantum",gps=5e20}}}
}

-- RNG Options Lists
local prngTypes = {"LCG", "math.random", "Random.new", "Mersenne Twister", "Xorshift"}
local csprngTypes = {
    "Sha-256", "ChaCha20", 
    "Sha-0", "Sha-1", "Sha-224", "Sha-384", "Sha-512", "Sha3-512",
    "ChaCha8", "ChaCha12", "ChaCha20-Poly1305", "XChaCha20-Poly1305",
    "ChaCha20-Poly1305 + AEAD", "ChaCha20 + Sha-512"
}

--------------------------------------------------------------------------------
-- LOGIC & FUNCTIONS (DARI KODE 2)
--------------------------------------------------------------------------------

local function detect_charset(pass)
	local sets = {
		{chars="abcdefghijklmnopqrstuvwxyz",size=26,name="lower"},
		{chars="ABCDEFGHIJKLMNOPQRSTUVWXYZ",size=26,name="upper"},
		{chars="0123456789",size=10,name="digits"},
		{chars="!@#$%^&*()-_=+[]{}|;:'\",.<>/?`~\\",size=32,name="symbols"}
	}
	local used = {}
	local total = 0
	for _, set in ipairs(sets) do
		for i = 1, #pass do
			local c = pass:sub(i,i)
			if set.chars:find(c, 1, true) then
				used[set.name] = true
				break
			end
		end
	end
	for _, set in ipairs(sets) do
		if used[set.name] then total = total + set.size end
	end
	if total == 0 then total = 26 end
	return total, used
end

local function entropy_bits(pass)
	local charset_size = detect_charset(pass)
	local L = #pass
	local bits = L * (math.log(charset_size) / math.log(2))
	return bits
end

local function search_space(pass)
	local charset_size = detect_charset(pass)
	local L = #pass
	return safe_pow(charset_size, L)
end

local function fmt_seconds(sec)
	local s = tonumber(sec) or 0
	if s ~= s then s = 0 end
	local units = {
		{"millennium", 60*60*24*365*1000},
		{"century", 60*60*24*365*100},
		{"decade", 60*60*24*365*10},
		{"year", 60*60*24*365},
		{"day", 60*60*24},
		{"hour", 60*60},
		{"minute", 60},
		{"second", 1},
		{"millisecond", 1e-3},
		{"microsecond", 1e-6},
		{"nanosecond", 1e-9},
		{"picosecond", 1e-12},
	}
	if s == 0 then return "0.000000 seconds" end
	for i, u in ipairs(units) do
		local name, val = u[1], u[2]
		if s >= val and val >= 1 then
			local v = s / val
			return string.format("%.6f %s%s", v, name, (v>1 and "s" or ""))
		elseif val < 1 and s >= val then
			local v = s / val
			return string.format("%.6f %s", v, name)
		end
	end
	return string.format("%.6f seconds", s)
end

local function human_readable(seconds)
	if seconds == 0 then return "instant" end
	return fmt_seconds(seconds)
end

local function pick_status(modeTable, seconds)
	local list = modeTable.statuses
	local max = #list
	local logsecs
	if seconds and seconds > 0 and seconds < math.huge then
		logsecs = math.log10(seconds + 1)
	else
		logsecs = 36
	end
	local score = clamp((logsecs) / 36, 0, 0.9999)
	local idx = math.floor(score * max) + 1
	if idx < 1 then idx = 1 end
	if idx > max then idx = max end
	return list[idx]
end

local function avg_guesses_to_find(space) return space / 2 end

local function compute_all_estimates(pass)
	local results = {}
	local space = search_space(pass)
	local avg = avg_guesses_to_find(space)
	local bits = entropy_bits(pass)
	for _, mode in ipairs(modes) do
		local modeRes = {mode = mode.label, spec = mode.spec, attacks = {}}
		for _, profile in ipairs(mode.attack_profiles) do
			local gps = profile.guesses_per_second
			local secs = (gps and gps > 0) and (avg / gps) or math.huge
			if secs ~= secs then secs = math.huge end
			table.insert(modeRes.attacks, {
				name = profile.name,
				guesses_per_second = gps,
				time_seconds = secs,
				time_human = human_readable(secs),
				status = pick_status(mode, secs),
				entropy_bits = bits,
				space = space,
				avg_guesses = avg,
				time_decimal6 = (secs==math.huge) and "∞" or string.format("%.6f", secs)
			})
		end
		table.insert(results, modeRes)
	end
	return results
end

local function detect_patterns(pass)
	local patterns = {}
	local p = pass:lower()
	for _, row in ipairs(keyboardRows) do
		for i=1,#row-2 do
			local sub = row:sub(i,i+2)
			if p:find(sub,1,true) then patterns.keyboard = sub break end
		end
		if patterns.keyboard then break end
	end
	for i=1,#pass-2 do
		local a = pass:sub(i,i)
		local b = pass:sub(i+1,i+1)
		local c = pass:sub(i+2,i+2)
		if a==b and b==c then patterns.repetition = a break end
	end
	local function is_sequence(s) if #s < 3 then return false end local inc, dec = true, true for i=2,#s do if s:byte(i) ~= s:byte(i-1) + 1 then inc = false end if s:byte(i) ~= s:byte(i-1) - 1 then dec = false end end return inc or dec end
	if is_sequence(pass) then patterns.sequence = true end
	local lower = pass:lower():gsub("[^%w]","")
	local map = {["4"]="a",["@"]="a",["3"]="e",["1"]="i",["!"]="i",["0"]="o",["5"]="s",["7"]="t"}
	local norm = {}
	for i=1,#lower do local c = lower:sub(i,i) norm[#norm+1] = (map[c] or c) end
	local normS = table.concat(norm)
	for _,cp in ipairs(commonPasswords) do
		if normS:find(cp,1,true) then patterns.common = cp break end
	end
	local digits = pass:match("%d%d%d%d")
	if digits then patterns.maybe_year = digits end
	return patterns
end

local function suggest_improvements(pass)
	local out = {}
	local L = #pass
	if L < 12 then out[#out+1] = "Make it at least 12 characters long for strong protection." end
	local cs = detect_charset(pass)
	if cs <= 26 then out[#out+1] = "Add uppercase letters, numbers, or symbols to increase charset." end
	local patterns = detect_patterns(pass)
	if patterns.keyboard then out[#out+1] = "Avoid simple keyboard patterns like '"..patterns.keyboard.."'" end
	if patterns.common then out[#out+1] = "Avoid common substrings like '"..patterns.common.."'" end
	if patterns.repetition then out[#out+1] = "Avoid repeated characters like '"..patterns.repetition.."'." end
	if patterns.maybe_year then out[#out+1] = "Avoid using years or dates like '"..patterns.maybe_year.."'" end
	if #out == 0 then out[#out+1] = "Looks good; consider using a multi-word passphrase for memorability." end
	return out
end

local function generate_password(style, length)
	style = style or "complex"
	length = length or 16
	local symbols = "!@#$%^&*()_+-=[]{};:,.<>?/\\|"
	local letters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
	local digits = "0123456789"
	local pool = letters..digits..symbols
	if style == "passphrase" then
		local parts = {}
		for i=1,4 do parts[#parts+1] = wordbank[math.random(1,#wordbank)] end
		local pw = table.concat(parts, "-")
		if #pw < length then pw = pw .. tostring(math.random(10,99)) end
		return pw
	elseif style == "readable" then
		local pw = ""
		for i=1,length do if i%3==0 then pw = pw .. tostring(math.random(0,9)) else pw = pw .. wordbank[math.random(1,#wordbank)]:sub(1,1) end end
		return pw
	else
		local pw = {}
		for i=1,length do pw[i] = pool:sub(math.random(1,#pool), math.random(1,#pool)) end
		return table.concat(pw)
	end
end

local function export_as_json(data) return HttpService:JSONEncode(data) end

local function safeCreate(class,props)
	local inst = Instance.new(class)
	for k,v in pairs(props or {}) do pcall(function() inst[k] = v end) end
	return inst
end

local function makeRounded(frame, radius) local c = Instance.new("UICorner", frame) c.CornerRadius = UDim.new(0, radius) return c end

--------------------------------------------------------------------------------
-- GUI CONSTRUCTION
--------------------------------------------------------------------------------

local function createUI()
	local screen = Instance.new("ScreenGui")
	screen.Name = "PasswordStudioMerged"
	screen.ResetOnSpawn = false
	screen.IgnoreGuiInset = true
	screen.Parent = PlayerGui

	local blur = Instance.new("BlurEffect", Lighting)
	blur.Name = "PS_StaticBlur"
	blur.Size = 15
	screen.Destroying:Connect(function() blur:Destroy() end)

	local center = safeCreate("Frame",{Parent=screen,Size=UDim2.new(0,980,0,620),Position=UDim2.new(0.5,-490,0.5,-310),BackgroundTransparency=1, ZIndex=1})
	local bg = safeCreate("Frame",{Parent=center,Size=UDim2.new(1,0,1,0),Position=UDim2.new(0,0,0,0),BackgroundColor3=themes["Dark Cyber"].bg,BorderSizePixel=0})
	makeRounded(bg,16)

	local glass = safeCreate("Frame",{Parent=bg,Size=UDim2.new(1,-28,1,-28),Position=UDim2.new(0,14,0,14),BackgroundTransparency=0.12,BorderSizePixel=0})
	makeRounded(glass,12)
	local gradient = Instance.new("UIGradient", glass)
	gradient.Rotation = 45
	gradient.Color = ColorSequence.new({ColorSequenceKeypoint.new(0, Color3.fromRGB(255,255,255)), ColorSequenceKeypoint.new(1, Color3.fromRGB(200,200,255))})
	gradient.Transparency = NumberSequence.new({NumberSequenceKeypoint.new(0,0.88), NumberSequenceKeypoint.new(1,0.92)})

	local header = safeCreate("Frame",{Parent=glass,Size=UDim2.new(1,0,0,72),Position=UDim2.new(0,0,0,0),BackgroundTransparency=1})
	local title = safeCreate("TextLabel",{Parent=header,Size=UDim2.new(0.5,0,1,0),Position=UDim2.new(0.02,0,0,0),BackgroundTransparency=1,Text="Password Studio",Font=Enum.Font.GothamBold,TextSize=30,TextColor3=themes["Dark Cyber"].text,TextXAlignment=Enum.TextXAlignment.Left})
	local subtitle = safeCreate("TextLabel",{Parent=header,Size=UDim2.new(0.48,-24,1,0),Position=UDim2.new(0.5,24,0,0),BackgroundTransparency=1,Text="Merged Lab · Live analysis · CSPRNG Simulation",Font=Enum.Font.Gotham,TextSize=14,TextColor3=Color3.fromRGB(190,190,200),TextXAlignment=Enum.TextXAlignment.Right})

	local tabBar = safeCreate("Frame",{Parent=glass,Size=UDim2.new(1,-48,0,36),Position=UDim2.new(0,24,0,72),BackgroundTransparency=1})
	local tabStudio = safeCreate("TextButton",{Parent=tabBar,Size=UDim2.new(0,140,1,0),Position=UDim2.new(0,0,0,0),Text="Studio",Font=Enum.Font.GothamBold,TextSize=16,BackgroundTransparency=1,TextColor3=themes["Dark Cyber"].text})
	local tabLab = safeCreate("TextButton",{Parent=tabBar,Size=UDim2.new(0,140,1,0),Position=UDim2.new(0,150,0,0),Text="Lab Mode",Font=Enum.Font.GothamBold,TextSize=16,BackgroundTransparency=1,TextColor3=themes["Dark Cyber"].text})
	local tabRng = safeCreate("TextButton",{Parent=tabBar,Size=UDim2.new(0,180,1,0),Position=UDim2.new(0,300,0,0),Text="RNG Output Tester",Font=Enum.Font.GothamBold,TextSize=16,BackgroundTransparency=1,TextColor3=themes["Dark Cyber"].text})
	local closeBtn = safeCreate("TextButton",{Parent=tabBar,Size=UDim2.new(0,36,0,36),Position=UDim2.new(1,-36,0,0),Text="X",Font=Enum.Font.GothamBold,TextSize=18,BackgroundTransparency=1,TextColor3=Color3.fromRGB(255,100,100)})

	local content = safeCreate("Frame",{Parent=glass,Size=UDim2.new(1,-48,1,-140),Position=UDim2.new(0,24,0,120),BackgroundTransparency=1})
	
	-- Page 1: Studio
	local studioPage = safeCreate("Frame",{Parent=content,Size=UDim2.new(1,0,1,0),Position=UDim2.new(0,0,0,0),BackgroundTransparency=1})
	
	-- Page 2: Lab
	local labPage = safeCreate("Frame",{Parent=content,Size=UDim2.new(1,0,1,0),Position=UDim2.new(0,0,0,0),Visible=false,BackgroundTransparency=1})
	
	-- Page 3: RNG Tester
	local rngPage = safeCreate("Frame",{Parent=content,Size=UDim2.new(1,0,1,0),Position=UDim2.new(0,0,0,0),Visible=false,BackgroundTransparency=1})

	-- STUDIO UI
	local container = safeCreate("Frame",{Parent=studioPage,Size=UDim2.new(1,0,0,120),Position=UDim2.new(0,0,0,0),BackgroundTransparency=1})
	local inputBox = safeCreate("TextBox",{Parent=container,Size=UDim2.new(0.72,0,0,48),Position=UDim2.new(0,0,0,12),TextEditable=true,TextMasked=true,Text="",Font=Enum.Font.Gotham,TextSize=18,PlaceholderText="Type or paste a password...",ClearTextOnFocus=false,BackgroundColor3=themes["Dark Cyber"].panel,TextColor3=themes["Dark Cyber"].text,BorderSizePixel=0})
	makeRounded(inputBox,10)
	local showBtn = safeCreate("TextButton",{Parent=container,Size=UDim2.new(0,68,0,36),Position=UDim2.new(0.74,8,0,12),Text="Show",Font=Enum.Font.Gotham,TextSize=14,BackgroundColor3=themes["Dark Cyber"].panel,TextColor3=themes["Dark Cyber"].text})
	makeRounded(showBtn,8)
	local genBtn = safeCreate("TextButton",{Parent=container,Size=UDim2.new(0,120,0,36),Position=UDim2.new(0.74,84,0,12),Text="Generate ▼",Font=Enum.Font.GothamBold,TextSize=14,BackgroundColor3=themes["Dark Cyber"].panel,TextColor3=themes["Dark Cyber"].text})
	makeRounded(genBtn,8)
	local copyBtn = safeCreate("TextButton",{Parent=container,Size=UDim2.new(0,84,0,36),Position=UDim2.new(0.74,212,0,12),Text="Copy",Font=Enum.Font.Gotham,TextSize=14,BackgroundColor3=themes["Dark Cyber"].panel,TextColor3=themes["Dark Cyber"].text})
	makeRounded(copyBtn,8)

	local leftPanel = safeCreate("Frame",{Parent=studioPage,Size=UDim2.new(0.62,0,1, -140),Position=UDim2.new(0.02,0,0.22,0),BackgroundTransparency=1})
	local rightPanel = safeCreate("Frame",{Parent=studioPage,Size=UDim2.new(0.34,0,1,-140),Position=UDim2.new(0.66,0,0.22,0),BackgroundTransparency=1})

	local strengthCard = safeCreate("Frame",{Parent=leftPanel,Size=UDim2.new(1,0,0,120),Position=UDim2.new(0,0,0,0),BackgroundColor3=themes["Dark Cyber"].panel,BorderSizePixel=0})
	makeRounded(strengthCard,10)
	local sbg = safeCreate("Frame",{Parent=strengthCard,Size=UDim2.new(0.98,0,0,18),Position=UDim2.new(0.01,0,0.62,0),BackgroundColor3=Color3.fromRGB(30,30,38)})
	makeRounded(sbg,8)
	local sbar = safeCreate("Frame",{Parent=sbg,Size=UDim2.new(0,4,1,0),Position=UDim2.new(0,0,0,0),BackgroundColor3=themes["Dark Cyber"].accent})
	makeRounded(sbar,8)
	local entropyLabel = safeCreate("TextLabel",{Parent=strengthCard,Size=UDim2.new(0.6,0,0,26),Position=UDim2.new(0.02,0,0.08,0),BackgroundTransparency=1,Text="Entropy: 0 bits",Font=Enum.Font.GothamBold,TextSize=16,TextColor3=themes["Dark Cyber"].text,TextXAlignment=Enum.TextXAlignment.Left})
	local strengthText = safeCreate("TextLabel",{Parent=strengthCard,Size=UDim2.new(0.36,0,0,26),Position=UDim2.new(0.62,0,0.08,0),BackgroundTransparency=1,Text="Strength: 0%",Font=Enum.Font.Gotham,TextSize=14,TextColor3=Color3.fromRGB(200,200,200),TextXAlignment=Enum.TextXAlignment.Right})

	local analysisCard = safeCreate("Frame",{Parent=leftPanel,Size=UDim2.new(1,0,0,260),Position=UDim2.new(0,0,0.22,0),BackgroundColor3=themes["Dark Cyber"].panel,BorderSizePixel=0})
	makeRounded(analysisCard,10)
	local statsText = safeCreate("TextLabel",{Parent=analysisCard,Size=UDim2.new(1,-20,0,96),Position=UDim2.new(0,10,0,36),BackgroundTransparency=1,Text="—",Font=Enum.Font.Gotham,TextSize=14,TextColor3=Color3.fromRGB(220,220,220),TextWrapped=true})

	local patternCard = safeCreate("Frame",{Parent=rightPanel,Size=UDim2.new(1,0,0,120),Position=UDim2.new(0,0,0,0),BackgroundColor3=themes["Dark Cyber"].panel})
	makeRounded(patternCard,10)
	local patternText = safeCreate("TextLabel",{Parent=patternCard,Size=UDim2.new(1,-20,0,80),Position=UDim2.new(0,10,0,36),BackgroundTransparency=1,Text="—",Font=Enum.Font.Gotham,TextSize=13,TextColor3=Color3.fromRGB(220,220,220),TextWrapped=true,TextXAlignment=Enum.TextXAlignment.Left})

	local suggestCard = safeCreate("Frame",{Parent=rightPanel,Size=UDim2.new(1,0,0,200),Position=UDim2.new(0,0,0.22,0),BackgroundColor3=themes["Dark Cyber"].panel})
	makeRounded(suggestCard,10)
	local suggestList = safeCreate("TextLabel",{Parent=suggestCard,Size=UDim2.new(1,-20,0,150),Position=UDim2.new(0,10,0,36),BackgroundTransparency=1,Text="—",Font=Enum.Font.Gotham,TextSize=13,TextColor3=Color3.fromRGB(230,230,230),TextWrapped=true,TextXAlignment=Enum.TextXAlignment.Left})

	-- LAB UI
	local labLeft = safeCreate("Frame",{Parent=labPage,Size=UDim2.new(0.62,0,1, -40),Position=UDim2.new(0.02,0,0,0),BackgroundTransparency=1})
	local labRight = safeCreate("Frame",{Parent=labPage,Size=UDim2.new(0.34,0,1,-40),Position=UDim2.new(0.66,0,0,0),BackgroundTransparency=1})

	local labTitle = safeCreate("TextLabel",{Parent=labLeft,Size=UDim2.new(1,0,0,30),Position=UDim2.new(0,0,0,0),BackgroundTransparency=1,Text="Lab: Attack Profiles & Estimates",Font=Enum.Font.GothamBold,TextSize=18,TextColor3=themes["Dark Cyber"].text,TextXAlignment=Enum.TextXAlignment.Left})
	local labList = safeCreate("ScrollingFrame",{Parent=labLeft,Size=UDim2.new(1,0,0,520),Position=UDim2.new(0,0,0,36),CanvasSize=UDim2.new(0,0,0,0),BackgroundTransparency=1,Active=true,ScrollBarThickness=6})
	local labLayout = safeCreate("UIListLayout",{Parent=labList,Padding=UDim.new(0,8)})

	local labSpec = safeCreate("TextLabel",{Parent=labRight,Size=UDim2.new(1,0,0,520),Position=UDim2.new(0,0,0,0),BackgroundColor3=themes["Dark Cyber"].panel,Text="Select a mode to view details",Font=Enum.Font.Gotham,TextSize=14,TextColor3=Color3.fromRGB(230,230,230),TextWrapped=true,TextXAlignment=Enum.TextXAlignment.Left})
	makeRounded(labSpec,10)

	-- RNG TESTER UI (DARI KODE 2 - Akan digantikan oleh Kode 1 Logic)
	local rngLeft = safeCreate("Frame",{Parent=rngPage,Size=UDim2.new(0.35,0,1,-20),Position=UDim2.new(0,0,0,10),BackgroundTransparency=1})
	local rngRight = safeCreate("Frame",{Parent=rngPage,Size=UDim2.new(0.62,0,1,-20),Position=UDim2.new(0.38,0,0,10),BackgroundTransparency=1})
	
	local rngConfigPanel = safeCreate("Frame",{Parent=rngLeft,Size=UDim2.new(1,0,1,0),BackgroundColor3=themes["Dark Cyber"].panel})
	makeRounded(rngConfigPanel,12)
	
	local rngTitle = safeCreate("TextLabel",{Parent=rngConfigPanel,Size=UDim2.new(1,-20,0,30),Position=UDim2.new(0,10,0,10),BackgroundTransparency=1,Text="Configuration",Font=Enum.Font.GothamBold,TextSize=16,TextColor3=themes["Dark Cyber"].text,TextXAlignment=Enum.TextXAlignment.Left})
	
	local rngTypeBtn = safeCreate("TextButton",{Parent=rngConfigPanel,Size=UDim2.new(0.9,0,0,36),Position=UDim2.new(0.05,0,0,50),Text="Mode: PRNG",Font=Enum.Font.Gotham,TextSize=14,BackgroundColor3=Color3.fromRGB(40,40,50),TextColor3=Color3.fromRGB(240,240,240)})
	makeRounded(rngTypeBtn,6)
	local rngAlgoBtn = safeCreate("TextButton",{Parent=rngConfigPanel,Size=UDim2.new(0.9,0,0,36),Position=UDim2.new(0.05,0,0,96),Text="Algorithm: LCG",Font=Enum.Font.Gotham,TextSize=14,BackgroundColor3=Color3.fromRGB(40,40,50),TextColor3=Color3.fromRGB(240,240,240)})
	makeRounded(rngAlgoBtn,6)
	
	local rngSeedBox = safeCreate("TextBox",{Parent=rngConfigPanel,Size=UDim2.new(0.9,0,0,36),Position=UDim2.new(0.05,0,0,142),Text="seed_123",Font=Enum.Font.Gotham,TextSize=14,PlaceholderText="Enter Seed",BackgroundColor3=Color3.fromRGB(40,40,50),TextColor3=Color3.fromRGB(240,240,240)}) -- Disesuaikan dengan Kode 1
	makeRounded(rngSeedBox,6)
	local rngLenBox = safeCreate("TextBox",{Parent=rngConfigPanel,Size=UDim2.new(0.9,0,0,36),Position=UDim2.new(0.05,0,0,188),Text="128",Font=Enum.Font.Gotham,TextSize=14,PlaceholderText="Length (Bytes)",BackgroundColor3=Color3.fromRGB(40,40,50),TextColor3=Color3.fromRGB(240,240,240)})
	makeRounded(rngLenBox,6)
	
	local rngActionBtn = safeCreate("TextButton",{Parent=rngConfigPanel,Size=UDim2.new(0.9,0,0,44),Position=UDim2.new(0.05,0,0,240),Text="GENERATE OUTPUT STREAM",Font=Enum.Font.GothamBold,TextSize=14,BackgroundColor3=themes["Dark Cyber"].accent,TextColor3=Color3.fromRGB(20,20,20)})
	makeRounded(rngActionBtn,8)
	
	local rngDesc = safeCreate("TextLabel",{Parent=rngConfigPanel,Size=UDim2.new(0.9,0,0,150),Position=UDim2.new(0.05,0,0,300),BackgroundTransparency=1,Text="Select an algorithm to simulate. PRNGs are fast but predictable. CSPRNGs use cryptographic primitives (ChaCha/SHA) for secure randomness.",Font=Enum.Font.Gotham,TextSize=12,TextColor3=Color3.fromRGB(180,180,180),TextWrapped=true,TextYAlignment=Enum.TextYAlignment.Top})

	local rngOutPanel = safeCreate("Frame",{Parent=rngRight,Size=UDim2.new(1,0,1,0),BackgroundColor3=themes["Dark Cyber"].panel})
	makeRounded(rngOutPanel,12)
	local rngOutTitle = safeCreate("TextLabel",{Parent=rngOutPanel,Size=UDim2.new(1,-20,0,30),Position=UDim2.new(0,10,0,10),BackgroundTransparency=1,Text="Output Stream (Hex Representation)",Font=Enum.Font.GothamBold,TextSize=16,TextColor3=themes["Dark Cyber"].text,TextXAlignment=Enum.TextXAlignment.Left})
	local rngScroll = safeCreate("ScrollingFrame",{Parent=rngOutPanel,Size=UDim2.new(1,-20,1,-100),Position=UDim2.new(0,10,0,45),BackgroundTransparency=1,CanvasSize=UDim2.new(0,0,0,0),ScrollBarThickness=6})
	local rngOutputText = safeCreate("TextLabel",{Parent=rngScroll,Size=UDim2.new(1,0,1,0),BackgroundTransparency=1,Text="Waiting for generation...",Font=Enum.Font.Code,TextSize=13,TextColor3=Color3.fromRGB(160,255,160),TextXAlignment=Enum.TextXAlignment.Left,TextYAlignment=Enum.TextYAlignment.Top,TextWrapped=true})
	local rngStats = safeCreate("TextLabel",{Parent=rngOutPanel,Size=UDim2.new(1,-20,0,40),Position=UDim2.new(0,10,1,-45),BackgroundTransparency=1,Text="Entropy estimate: -",Font=Enum.Font.Gotham,TextSize=13,TextColor3=Color3.fromRGB(200,200,200),TextXAlignment=Enum.TextXAlignment.Right})
    
    local state = {lastTick=0,throttle=0.14,exportCache="", currentMode=1, rngMode="PRNG", rngAlgo="LCG"}

	-- FOOTER
	local bottomBar = safeCreate("Frame",{Parent=glass,Size=UDim2.new(1,-48,0,36),Position=UDim2.new(0,24,1,-48),BackgroundTransparency=1})
	local modeBtn = safeCreate("TextButton",{Parent=bottomBar,Size=UDim2.new(0,220,1,0),Position=UDim2.new(0,0,0,0),Text="Mode: Gaming PC",Font=Enum.Font.Gotham,TextSize=14,BackgroundTransparency=1,TextColor3=themes["Dark Cyber"].text})
	local exportBtn = safeCreate("TextButton",{Parent=bottomBar,Size=UDim2.new(0,120,1,0),Position=UDim2.new(0.26,0,0,0),Text="Export JSON",Font=Enum.Font.Gotham,TextSize=14,BackgroundTransparency=1,TextColor3=themes["Dark Cyber"].text})
	local themeBtn = safeCreate("TextButton",{Parent=bottomBar,Size=UDim2.new(0,160,1,0),Position=UDim2.new(0.46,0,0,0),Text="Theme: Dark Cyber ▼",Font=Enum.Font.Gotham,TextSize=14,BackgroundTransparency=1,TextColor3=themes["Dark Cyber"].text})
	local soundToggle = safeCreate("TextButton",{Parent=bottomBar,Size=UDim2.new(0,120,1,0),Position=UDim2.new(0.7,0,0,0),Text="Sound: On",Font=Enum.Font.Gotham,TextSize=14,BackgroundTransparency=1,TextColor3=themes["Dark Cyber"].text})
	local exportCopy = safeCreate("TextButton",{Parent=bottomBar,Size=UDim2.new(0,120,1,0),Position=UDim2.new(0.86,0,0,0),Text="Copy Export",Font=Enum.Font.Gotham,TextSize=14,BackgroundTransparency=1,TextColor3=themes["Dark Cyber"].text})

	local sounds = {}
	local function createSound(id,vol) local s = Instance.new("Sound", center) s.SoundId = id s.Volume = vol or 0.6 return s end
	sounds.tick = createSound("rbxassetid://142070127",0.5)
	sounds.pop = createSound("rbxassetid://142070176",0.6)
	local soundOn = true

	local function play(name) if not soundOn then return end local s = sounds[name] if s then pcall(function() s:Play() end) end end

	local currentMode = 1
	local currentTheme = "Dark Cyber"
	
	-- Theme Application Function
	local function applyTheme(name)
		local t = themes[name] or themes["Dark Cyber"]
		bg.BackgroundColor3 = t.bg
		glass.BackgroundColor3 = t.panel
		title.TextColor3 = t.text
		subtitle.TextColor3 = Color3.fromRGB(190,190,200)
		inputBox.BackgroundColor3 = t.panel
		inputBox.TextColor3 = t.text
		showBtn.BackgroundColor3 = t.panel
		genBtn.BackgroundColor3 = t.panel
		copyBtn.BackgroundColor3 = t.panel
		sbar.BackgroundColor3 = t.accent
		entropyLabel.TextColor3 = t.text
		strengthText.TextColor3 = t.text
		statsText.TextColor3 = Color3.fromRGB(220,220,220)
		patternText.TextColor3 = Color3.fromRGB(230,230,230)
		suggestList.TextColor3 = Color3.fromRGB(230,230,230)
		labSpec.BackgroundColor3 = t.panel
		
		-- RNG Page Elements
		rngConfigPanel.BackgroundColor3 = t.panel
		rngOutPanel.BackgroundColor3 = t.panel
		rngTitle.TextColor3 = t.text
		rngOutTitle.TextColor3 = t.text
		rngActionBtn.BackgroundColor3 = t.accent
		rngTypeBtn.BackgroundColor3 = Color3.fromRGB(40,40,50)
		rngAlgoBtn.BackgroundColor3 = Color3.fromRGB(40,40,50)
		rngSeedBox.BackgroundColor3 = Color3.fromRGB(40,40,50)
		rngLenBox.BackgroundColor3 = Color3.fromRGB(40,40,50)
		
		themeBtn.Text = "Theme: "..name.." ▼"
		currentTheme = name
	end
	applyTheme(currentTheme)

	local function updateStudioUI(pass)
		local L = #pass
		local cs,_ = detect_charset(pass)
		local bits = entropy_bits(pass)
		entropyLabel.Text = ("Entropy: %.2f bits"):format(bits)
		local pct = clamp(bits / 128,0,1)
		strengthText.Text = ("Strength: %d%%"):format(math.floor(pct*100))
		local width = math.max(6, math.floor(pct * (sbg.AbsoluteSize.X - 4)))
		local tweenInfo = TweenInfo.new(0.25, Enum.EasingStyle.Quad, Enum.EasingDirection.Out)
		pcall(function() TweenService:Create(sbar, tweenInfo, {Size = UDim2.new(0, width, 1, 0)}):Play() end)
		local color
		if pct < 0.25 then color = Color3.fromRGB(220,80,80) elseif pct < 0.5 then color = Color3.fromRGB(230,150,70) elseif pct < 0.8 then color = Color3.fromRGB(120,200,120) else color = Color3.fromRGB(60,200,200) end
		sbar.BackgroundColor3 = color
		local stats = {}
		stats[#stats+1] = ("Length: %d"):format(L)
		stats[#stats+1] = ("Charset size: %d"):format(cs)
		stats[#stats+1] = ("Entropy bits: "..round(bits,2))
		local space = search_space(pass)
		if space == math.huge then stats[#stats+1] = ("Search space: "..fmt_scientific(10^(L * math.log10(cs)))) else stats[#stats+1] = ("Search space: "..format_commas(space)) end
		local avg = (space==math.huge) and "∞" or format_commas(space/2)
		stats[#stats+1] = ("Avg guesses (approx): "..avg)
		statsText.Text = table.concat(stats, "\n")
		local patterns = detect_patterns(pass)
		local pattLines = {}
		if next(patterns) == nil then pattLines[#pattLines+1] = "No obvious weak patterns detected." else for k,v in pairs(patterns) do pattLines[#pattLines+1] = ("• %s: %s"):format(k, tostring(v)) end end
		patternText.Text = table.concat(pattLines, "\n")
		local sug = suggest_improvements(pass)
		suggestList.Text = "• "..table.concat(sug, "\n• ")
		state.exportCache = export_as_json({computed={pass=pass,length=L,charset=cs,bits=bits,space=space},patterns=patterns,suggestions=sug,mode=attackModes[currentMode].label,theme=currentTheme})
	end

	local function buildLabItems(pass)
		for _,c in ipairs(labList:GetChildren()) do if not c:IsA("UIListLayout") then c:Destroy() end end
		local all = compute_all_estimates(pass)
		local ysize = 0
		for _,modeRes in ipairs(all) do
			local block = safeCreate("Frame",{Parent=labList,Size=UDim2.new(1,-8,0,120),BackgroundColor3=themes[currentTheme].panel})
			makeRounded(block,8)
			local t = safeCreate("TextLabel",{Parent=block,Size=UDim2.new(1,-12,0,26),Position=UDim2.new(0,6,0,6),BackgroundTransparency=1,Text=modeRes.mode,Font=Enum.Font.GothamBold,TextSize=14,TextColor3=themes[currentTheme].text,TextXAlignment=Enum.TextXAlignment.Left})
			local s = safeCreate("TextLabel",{Parent=block,Size=UDim2.new(1,-12,0,18),Position=UDim2.new(0,6,0,34),BackgroundTransparency=1,Text=("Entropy: %.2f bits • Search space: %s"):format(modeRes.attacks[1].entropy_bits, (modeRes.attacks[1].space==math.huge and fmt_scientific(10^(#pass * math.log10(select(1, detect_charset(pass))))) or format_commas(modeRes.attacks[1].space))),Font=Enum.Font.Gotham,TextSize=12,TextColor3=Color3.fromRGB(200,200,200),TextXAlignment=Enum.TextXAlignment.Left})
			local y = 56
			for i,a in ipairs(modeRes.attacks) do
				local line = safeCreate("TextLabel",{Parent=block,Size=UDim2.new(1,-12,0,14),Position=UDim2.new(0,6,0,y),BackgroundTransparency=1,Text=(a.name.." | rate: "..fmt_scientific(a.guesses_per_second).." g/s | avg time: "..a.time_human),Font=Enum.Font.Gotham,TextSize=12,TextColor3=Color3.fromRGB(220,220,220),TextXAlignment=Enum.TextXAlignment.Left})
				y = y + 16
			end
			block.Size = UDim2.new(1,-8,0,y) -- Adjust height dynamically
			ysize = ysize + block.Size.Y.Offset + 8
		end
		labList.CanvasSize = UDim2.new(0,0,0, ysize + 12)
	end

	inputBox:GetPropertyChangedSignal("Text"):Connect(function()
		local now = os.clock()
		if now - state.lastTick < state.throttle then return end
		state.lastTick = now
		updateStudioUI(inputBox.Text)
		if labPage.Visible then buildLabItems(inputBox.Text) end
	end)

	showBtn.MouseButton1Click:Connect(function()
		inputBox.TextMasked = not inputBox.TextMasked
		showBtn.Text = inputBox.TextMasked and "Show" or "Hide"
		play("tick")
	end)
	
	closeBtn.MouseButton1Click:Connect(function()
		screen:Destroy()
	end)

    -- GEN MENU
	local genMenu
	genBtn.MouseButton1Click:Connect(function()
		if genMenu and genMenu.Parent then genMenu:Destroy() genMenu = nil return end
		genMenu = safeCreate("Frame",{Parent=center,Size=UDim2.new(0,260,0,160),Position=UDim2.new(0,380,0,140),BackgroundColor3=themes[currentTheme].panel, ZIndex=10})
		makeRounded(genMenu,10)
		local g1 = safeCreate("TextButton",{Parent=genMenu,Size=UDim2.new(1,0,0,40),Position=UDim2.new(0,0,0,0),Text="Complex 16 chars",Font=Enum.Font.Gotham,TextSize=14, ZIndex=11})
		local g2 = safeCreate("TextButton",{Parent=genMenu,Size=UDim2.new(1,0,0,40),Position=UDim2.new(0,0,0,40),Text="Readable passphrase",Font=Enum.Font.Gotham,TextSize=14, ZIndex=11})
		local g3 = safeCreate("TextButton",{Parent=genMenu,Size=UDim2.new(1,0,0,40),Position=UDim2.new(0,0,0,80),Text="Short memorable",Font=Enum.Font.Gotham,TextSize=14, ZIndex=11})
		local g4 = safeCreate("TextButton",{Parent=genMenu,Size=UDim2.new(1,0,0,40),Position=UDim2.new(0,0,0,120),Text="Close",Font=Enum.Font.Gotham,TextSize=14, ZIndex=11})
		local function pickStyle(s,l)
			local pw = generate_password(s,l)
			inputBox.Text = pw
			updateStudioUI(pw)
			if labPage.Visible then buildLabItems(pw) end
			play("pop")
			genMenu:Destroy()
			genMenu = nil
		end
		g1.MouseButton1Click:Connect(function() pickStyle("complex",16) end)
		g2.MouseButton1Click:Connect(function() pickStyle("passphrase",20) end)
		g3.MouseButton1Click:Connect(function() pickStyle("readable",12) end)
		g4.MouseButton1Click:Connect(function() if genMenu then genMenu:Destroy() genMenu = nil end end)
	end)

	copyBtn.MouseButton1Click:Connect(function() pcall(function() setclipboard(inputBox.Text) end) play("tick") end)

	modeBtn.MouseButton1Click:Connect(function()
		currentMode = currentMode + 1
		if currentMode > #attackModes then currentMode = 1 end
		modeBtn.Text = "Mode: "..attackModes[currentMode].label
		updateStudioUI(inputBox.Text)
		if labPage.Visible then buildLabItems(inputBox.Text) end
		play("tick")
	end)
	
	-- RNG Logic (Menggunakan Logic Code 1)
	rngTypeBtn.MouseButton1Click:Connect(function()
	    if state.rngMode == "PRNG" then 
            state.rngMode = "CSPRNG" 
            state.rngAlgo = csprngTypes[1] 
        else 
            state.rngMode = "PRNG" 
            state.rngAlgo = prngTypes[1]
        end
	    rngTypeBtn.Text = "Mode: "..state.rngMode
	    rngAlgoBtn.Text = "Algorithm: "..state.rngAlgo
	    play("tick")
	end)
	
	rngAlgoBtn.MouseButton1Click:Connect(function()
	    local list = (state.rngMode == "PRNG" and prngTypes or csprngTypes)
        
        -- Create Dropdown Frame directly in ScreenGui for ZIndex priority
        local menu = Instance.new("Frame", screen)
        menu.Size = UDim2.new(0, 240, 0, math.min(#list * 32, 400))
        -- Positioned relative to rngAlgoBtn but in ScreenGui space (approx)
        local absPos = rngAlgoBtn.AbsolutePosition
        local offset = center.AbsolutePosition
        menu.Position = UDim2.new(0, absPos.X - offset.X, 0, absPos.Y - offset.Y + rngAlgoBtn.AbsoluteSize.Y)
        
        menu.BackgroundColor3 = themes[currentTheme].panel
        menu.ZIndex = 100 -- MAX ZINDEX
        menu.BorderSizePixel = 2
        menu.BorderColor3 = themes[currentTheme].accent
        makeRounded(menu, 8)
        
        local s = safeCreate("ScrollingFrame",{Parent=menu,Size=UDim2.new(1,0,1,0),CanvasSize=UDim2.new(0,0,0,#list*32),BackgroundTransparency=1,ScrollBarThickness=4, ZIndex=101})
        
        for i, alg in ipairs(list) do
            local b = safeCreate("TextButton",{Parent=s,Size=UDim2.new(1,0,0,32),Position=UDim2.new(0,0,0,(i-1)*32),Text=alg,Font=Enum.Font.Gotham,TextSize=14,TextColor3=Color3.fromRGB(220,220,220),BackgroundTransparency=1, ZIndex=102})
            b.MouseButton1Click:Connect(function()
                state.rngAlgo = alg
                rngAlgoBtn.Text = "Algorithm: " .. alg
                menu:Destroy()
                play("pop")
            end)
        end
        
        -- Close if clicked outside (simple giant button behind)
        local closer = Instance.new("TextButton", screen)
        closer.Size = UDim2.new(1,0,1,0)
        closer.BackgroundTransparency = 1
        closer.Text = ""
        closer.ZIndex = 99
        closer.MouseButton1Click:Connect(function() menu:Destroy() closer:Destroy() end)
	end)
	
	rngActionBtn.MouseButton1Click:Connect(function()
	    local seed = rngSeedBox.Text; if seed == "" then seed = tostring(os.clock()) end
	    local len = tonumber(rngLenBox.Text) or 64
	    len = clamp(len, 1, 4096)
	    
	    rngOutputText.Text = "Generating..."
	    task.wait(0.05)
	    
	    local outHex = GenerateRNG(state.rngMode, state.rngAlgo, seed, len)
	    rngOutputText.Text = outHex
	    
	    -- Quick Entropy estimate of output (Hex)
	    local cs, used = 0, {}
	    for i=1,#outHex do local c = outHex:sub(i,i) if not used[c] then used[c]=true cs=cs+1 end end
	    local bits = #outHex * (math.log(cs)/math.log(2))
	    rngStats.Text = string.format("Entropy estimate: %.2f bits (on hex stream)", bits)
	    
	    -- Resize text to fit
	    local txtSize = game:GetService("TextService"):GetTextSize(rngOutputText.Text, 13, Enum.Font.Code, Vector2.new(rngScroll.AbsoluteSize.X, 99999))
	    rngScroll.CanvasSize = UDim2.new(0,0,0, txtSize.Y + 20)
	    rngOutputText.Size = UDim2.new(1,0,0, txtSize.Y + 20)
	    
	    play("pop")
	end)

	exportBtn.MouseButton1Click:Connect(function()
		local j = state.exportCache ~= "" and state.exportCache or export_as_json({computed={pass=inputBox.Text}})
		try_set_clipboard(j)
		play("pop")
	end)

	exportCopy.MouseButton1Click:Connect(function()
		try_set_clipboard(state.exportCache)
		play("tick")
	end)

	themeBtn.MouseButton1Click:Connect(function()
		local keys = {}
		for k,_ in pairs(themes) do keys[#keys+1] = k end
		local menu = Instance.new("Frame", center)
		menu.Size = UDim2.new(0,160,0,#keys*36)
		menu.Position = UDim2.new(0,420,0,460)
		menu.BackgroundColor3 = themes[currentTheme].panel
		menu.ZIndex = 10
		makeRounded(menu,8)
		for i,k in ipairs(keys) do
			local b = safeCreate("TextButton",{Parent=menu,Size=UDim2.new(1,0,0,36),Position=UDim2.new(0,0,0,(i-1)*36),Text=k,Font=Enum.Font.Gotham,TextSize=14, ZIndex=11})
			b.MouseButton1Click:Connect(function()
				applyTheme(k)
				menu:Destroy()
				play("pop")
				updateStudioUI(inputBox.Text)
			end)
		end
	end)

	soundToggle.MouseButton1Click:Connect(function()
		soundOn = not soundOn
		soundToggle.Text = (soundOn and "Sound: On" or "Sound: Off")
		play("tick")
	end)

	tabStudio.MouseButton1Click:Connect(function()
		studioPage.Visible = true
		labPage.Visible = false
		rngPage.Visible = false
		play("tick")
	end)
	tabLab.MouseButton1Click:Connect(function()
		studioPage.Visible = false
		labPage.Visible = true
		rngPage.Visible = false
		buildLabItems(inputBox.Text)
		play("tick")
	end)
	tabRng.MouseButton1Click:Connect(function()
		studioPage.Visible = false
		labPage.Visible = false
		rngPage.Visible = true
		play("tick")
	end)
	
	local dragging, dragInput, dragStart, startPos
	local function update(input)
		local delta = input.Position - dragStart
		center.Position = UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
	end
	header.InputBegan:Connect(function(input)
		if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
			dragging = true
			dragStart = input.Position
			startPos = center.Position
			input.Changed:Connect(function()
				if input.UserInputState == Enum.UserInputState.End then dragging = false end
			end)
		end
	end)
	header.InputChanged:Connect(function(input)
		if input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch then
			dragInput = input
		end
	end)
	UserInputService.InputChanged:Connect(function(input)
		if input == dragInput and dragging then update(input) end
	end)

	updateStudioUI("")
	buildLabItems("")
	return screen
end

local gui = createUI()
