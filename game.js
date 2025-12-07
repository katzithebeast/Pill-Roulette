import * as THREE from 'three';
import { FBXLoader } from 'three/addons/loaders/FBXLoader.js';
import { OBJLoader } from 'three/addons/loaders/OBJLoader.js';
import { GLTFLoader } from 'three/addons/loaders/GLTFLoader.js';
import * as CANNON from 'cannon-es';

// --- KONFIGURACE A STAV HRY ---
const STATE = {
    START: 0,
    WAITING_FOR_TOSS: 1,
    COIN_FLYING: 1.5,
    COIN_LANDED: 1.8, // Nový stav: mince leží a čeká na odkliknutí
    PLAYER_TURN: 2,
    ENEMY_TURN: 3,
    GAME_OVER: 4
};

let gameState = STATE.START;
let playerHP = 5;
let enemyHP = 5;
let playerToxicity = 0; // Systém toxikace pro hráče
let enemyToxicity = 0; // Systém toxikace pro oponenta
let isBottleOpen = false;

// Systém pro itemy
let injectorToxicityReduction = 0; // Kolik toxifikace se neguje z příští pilulky
let isTesterActive = false; // Zda je tester aktivní
let testedPill = null; // Testovaná pilulka
let pliersToxicityAdded = 0; // Kolik toxifikace přidaly kleště (pro negaci zubem)
let isBrainActive = false; // Zda je brain aktivní a čeká na výběr pilulky
let isCandyActive = false; // Zda je candy aktivní (místo pilulky)
let isHammerActive = false; // Zda je hammer aktivní a čeká na výběr pilulky k zničení

// Stav víčka
const CAP_STATE = {
    ATTACHED: 0,
    UNSCREWING: 1,
    FALLING: 2
};
let capState = CAP_STATE.ATTACHED;
let capUnscrewProgress = 0; 

// Fyzika
let world;
const timeStep = 1 / 60;
let lastCallTime;
const objectsToUpdate = []; // { mesh, body, isCoin, ... }
const playerItems = []; // Itemy vlastněné hráčem { type, mesh, body, owner: 'player' }
const enemyItems = []; // Itemy vlastněné oponentem { type, mesh, body, owner: 'enemy' }

// Scéna
let scene, camera, renderer;
let shopScene, shopCamera, shopRenderer; // Shop 3D scéna
let raycaster, mouse;
let bottleBody, bottleGroup;
let capBody, capMesh; 
let coinBody, coinMesh;
let injectorBody, injectorGroup;
let testerBody, testerGroup;
let pliersBody, pliersGroup;
let toothBody, toothGroup;
let candyBody, candyGroup;
let brainBody, brainGroup;
let leechBody, leechGroup;
let hammerBody, hammerGroup;
let hearthBody, hearthGroup; 
let previewCoinMesh; // Levitující mince v menu
let mouseConstraint; // Pro drag & drop
let mouseTargetPos = new CANNON.Vec3(0,0,0); // Cíl pro vyhlazený pohyb
let currentLift = 0; // Aktuální výška zvednutí (pro plynulou transici)
let isDragging = false;
let draggingObject = null; // 'bottle', 'cap', 'pill', 'injector', 'tester', 'pliers', 'tooth', 'candy', 'brain', 'leech', 'hammer', 'hearth', nebo null
let lastHoverCheck = 0; // Throttling pro hover efekt
const HOVER_CHECK_INTERVAL = 50; // Kontrolovat hover pouze každých 50ms

// Pro drag pilulek - rozlišení kliknutí vs drag
let potentialPillGroup = null; // Potenciální pilulka k tažení
let potentialPillBody = null; // Těleso pilulky
let mouseDownPos = { x: 0, y: 0 }; // Počáteční pozice myši při mousedown
let hasMoved = false; // Zda se myš pohnula od mousedown
const DRAG_THRESHOLD = 5; // Prahová hodnota v pixelech pro rozpoznání drag

// Stůl - dvě poloviny pro otevírání (levá a pravá), které se rozdělí uprostřed
let tableLeftMesh, tableRightMesh;
let tableLeftBody, tableRightBody;
// Podlaha
let floorMesh = null;
let roundNumber = 1; // Číslo kola (1 = první kolo s hodem mincí)
let isTableOpening = false; // Flag pro otevírání stolu
let tableTiltAngle = 0; // Aktuální úhel náklonu stolu (pro aplikaci síly)
let currentRoundPills = []; // Fixní seznam všech pilulek spawnnutých v aktuálním kole

// UI
const uiStatus = document.getElementById('game-status');
const uiPlayerHP = document.getElementById('player-hp');
const uiEnemyHP = document.getElementById('enemy-hp');
const uiPlayerToxicity = document.getElementById('player-toxicity');
const uiEnemyToxicity = document.getElementById('enemy-toxicity');
const uiPillStats = document.getElementById('pill-stats');

// Modely (uložené pro klonování)
let pillModel = null;
let pillTabletModel = null; // Pill tablet model (pro vitamin pills ve 2. kole)
let vitaminPillModel = null; // Vitamin pill model (pro vitamin pills ve 3. kole)
let bottleModelData = null; // Data pro pozdější spawn
let injectorModelData = null; // Data pro injector
let testerModelData = null; // Data pro tester
let pliersModelData = null; // Data pro kleště
let toothModelData = null; // Data pro zub
let candyModelData = null; // Data pro candy
let brainModelData = null; // Data pro brain
let leechModelData = null; // Data pro leech
let hammerModelData = null; // Data pro hammer
let hearthModelData = null; // Data pro hearth
let zombieGroup = null; // Zombie oponent
let zombieMixer = null; // Animation mixer pro zombie animace
let wobbleTime = 0; // PS1 HORROR STYL: Čas pro wobble efekt

// Trackery pro HP a toxicitu
let playerTrackerMesh = null;
let enemyTrackerMesh = null;
let trackerBaseTexture = null; // Základní textura tracker.png
let playerTrackerTexture = null; // Dynamická textura pro hráče
let enemyTrackerTexture = null; // Dynamická textura pro oponenta

// Debug hodnoty pro zombie
let zombieDebugPos = { x: -0.100, y: -1.400, z: -3.500 };
let zombieDebugRot = { x: -1.570, y: 0.000, z: 0.090 };
let zombieDebugScale = 4.700;
let enemyMouthHeight = 1.0; // Výška úst pro oponenta (relativní k zombie scale)
let bottleCapScale = 1.0; // Měřítko lahve a víčka (zmenšeno o třetinu z 1.5)
let tableDebugRotationX = 0.0; // Debug rotace stolu kolem X osy (pro obě poloviny)
let isDebugMode = false;

// Don't start game immediately - wait for menu
// init();
// animate();

// Loading tracking
let modelsToLoad = 15; // Celkový počet modelů/textur k načtení
let modelsLoaded = 0;
let isLoadingComplete = false;
let loadingStartTime = 0; // Čas začátku načítání
const MIN_LOADING_TIME = 1500; // Minimální doba zobrazení loading screenu (ms)

// Function to update loading progress
function updateLoadingProgress(modelName) {
    modelsLoaded++;
    const progress = (modelsLoaded / modelsToLoad) * 100;
    
    const loadingBar = document.getElementById('loading-bar');
    const loadingText = document.getElementById('loading-text');
    
    if (loadingBar) {
        loadingBar.style.width = progress + '%';
    }
    if (loadingText) {
        loadingText.textContent = 'Loading: ' + modelName + '... (' + modelsLoaded + '/' + modelsToLoad + ')';
    }
    
    // Check if all models are loaded
    if (modelsLoaded >= modelsToLoad && !isLoadingComplete) {
        isLoadingComplete = true;
        finishLoading();
    }
}

// Function to finish loading and show game
function finishLoading() {
    const loadingScreen = document.getElementById('loading-screen');
    const rendererElement = renderer ? renderer.domElement : null;
    
    // Calculate elapsed time
    const elapsedTime = Date.now() - loadingStartTime;
    const remainingTime = Math.max(0, MIN_LOADING_TIME - elapsedTime);
    
    // Wait for minimum loading time to ensure loading screen is visible
    setTimeout(() => {
        // Hide loading screen
        if (loadingScreen) {
            loadingScreen.style.display = 'none';
        }
        
        // Show renderer
        if (rendererElement) {
            rendererElement.style.display = 'block';
        }
        
        // Show game UI
        if (window.showGameUI) {
            window.showGameUI();
        }
        
        // Start coin toss if bottle is loaded
        if (bottleModelData && gameState === STATE.START) {
            startCoinToss();
        }
    }, remainingTime + 100); // +100ms pro jistotu
}

// Function to start game from menu
window.startGame = function() {
    // Record loading start time
    loadingStartTime = Date.now();
    
    // Show loading screen immediately
    const loadingScreen = document.getElementById('loading-screen');
    const rendererElement = renderer ? renderer.domElement : null;
    
    if (loadingScreen) {
        loadingScreen.style.display = 'flex'; // Use flex instead of block for better centering
    }
    
    // Hide renderer until loading is complete
    if (rendererElement) {
        rendererElement.style.display = 'none';
    }
    
    // Reset loading state
    modelsLoaded = 0;
    isLoadingComplete = false;
    const loadingBar = document.getElementById('loading-bar');
    const loadingText = document.getElementById('loading-text');
    if (loadingBar) loadingBar.style.width = '0%';
    if (loadingText) loadingText.textContent = 'Initializing...';
    
    // Small delay to ensure loading screen is visible before starting init
    setTimeout(() => {
        if (!window.gameInitialized) {
            init();
            window.gameInitialized = true;
        }
        if (!window.animationRunning) {
            animate();
            window.animationRunning = true;
        }
        gameState = STATE.START;
    }, 50);
};

// Function to reset game (for GIVE UP)
window.resetGame = function() {
    // Reset game state
    gameState = STATE.START;
    playerHP = 5;
    enemyHP = 5;
    playerToxicity = 0;
    enemyToxicity = 0;
    isBottleOpen = false;
    roundNumber = 1;
    
    // Reset item states
    injectorToxicityReduction = 0;
    isTesterActive = false;
    testedPill = null;
    pliersToxicityAdded = 0;
    isBrainActive = false;
    isCandyActive = false;
    isHammerActive = false;
    isHearthActive = false;
    
    // Clear items
    playerItems.length = 0;
    enemyItems.length = 0;
    
    // Remove all objects from scene
    if (objectsToUpdate) {
        objectsToUpdate.forEach(obj => {
            if (obj.mesh) {
                scene.remove(obj.mesh);
            }
            if (obj.body) {
                world.removeBody(obj.body);
            }
        });
        objectsToUpdate.length = 0;
    }
    
    // Remove bottle and cap if they exist
    if (bottleGroup) {
        scene.remove(bottleGroup);
        bottleGroup = null;
    }
    if (bottleBody) {
        world.removeBody(bottleBody);
        bottleBody = null;
    }
    if (capMesh) {
        scene.remove(capMesh);
        capMesh = null;
    }
    if (capBody) {
        world.removeBody(capBody);
        capBody = null;
    }
    
    // Remove coin if exists
    if (coinMesh) {
        scene.remove(coinMesh);
        coinMesh = null;
    }
    if (coinBody) {
        world.removeBody(coinBody);
        coinBody = null;
    }
    
    // Update UI
    if (window.updateUI) {
        updateUI();
    }
};

// Inicializovat debug mód po načtení DOMu
setTimeout(() => {
    if (document.getElementById('debug-toggle')) {
        initDebugMode();
    }
}, 100);

// Inicializovat debug mód po načtení DOMu
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', initDebugMode);
} else {
    // DOM je už načtený, zavolat okamžitě
    setTimeout(initDebugMode, 100);
}
initDebugMode();

function init() {
    // Globální error handler pro zobrazení chyb na obrazovce
    window.onerror = function(message, source, lineno, colno, error) {
        const status = document.getElementById('game-status');
        if(status) {
            status.style.display = 'block';
            status.style.color = 'red';
            status.innerText = "JS ERROR: " + message;
        }
    };

    // 1. INIT FYZIKY
    world = new CANNON.World();
    world.gravity.set(0, -9.82, 0);
    world.solver.iterations = 10; // Snížit počet iterací fyziky pro výkon 
    const defaultMaterial = new CANNON.Material('default');
    const defaultContactMaterial = new CANNON.ContactMaterial(defaultMaterial, defaultMaterial, {
        friction: 0.6,   // Vyšší tření
        restitution: 0.1, // Malá odrazivost (tlumí skákání)
        contactEquationStiffness: 1e8,
        contactEquationRelaxation: 3
    });
    world.addContactMaterial(defaultContactMaterial);
    world.defaultMaterial = defaultMaterial;

    // 2. INIT THREE.JS
    scene = new THREE.Scene();
    scene.background = new THREE.Color(0x000000); // Černé pozadí pro hororový efekt

    camera = new THREE.PerspectiveCamera(45, window.innerWidth / window.innerHeight, 0.1, 100);
    camera.position.set(0, 9, 8); 
    camera.lookAt(0, 0, 0);

    const ambientLight = new THREE.AmbientLight(0xffffff, 1.0); // Více ambient světla místo stínů
    scene.add(ambientLight);
    const dirLight = new THREE.DirectionalLight(0xffffff, 0.8);
    dirLight.position.set(5, 10, 5);
    dirLight.castShadow = false; // Vypnout stíny pro výkon
    scene.add(dirLight);

    // PS1 HORROR STYL: Low resolution rendering (trash quality)
    renderer = new THREE.WebGLRenderer({ 
        antialias: false, // Vypnout antialiasing pro pixelizaci
        powerPreference: "low-power" // Nižší výkon pro PS1 styl
    });
    // Snížit rozlišení rendereru na polovinu pro PS1 efekt
    const ps1Scale = 0.5; // 50% rozlišení
    renderer.setSize(window.innerWidth * ps1Scale, window.innerHeight * ps1Scale, false);
    renderer.domElement.style.width = '100%';
    renderer.domElement.style.height = '100%';
    renderer.domElement.style.imageRendering = 'pixelated'; // Pixel-perfect upscaling
    renderer.shadowMap.enabled = false;
    renderer.shadowMap.type = THREE.BasicShadowMap;
    // Hide renderer initially - will be shown after loading
    renderer.domElement.style.display = 'none';
    document.body.appendChild(renderer.domElement);

    raycaster = new THREE.Raycaster();
    mouse = new THREE.Vector2();
    window.addEventListener('mousemove', onMouseMove);
    // window.addEventListener('click', onMouseClick); // Smazáno - nahrazeno mousedown
    window.addEventListener('resize', onWindowResize);

    // 3. PROSTŘEDÍ
    createEnvironment();

    // Nastavit eventy pro drag
    window.addEventListener('mousedown', onMouseDown);
    window.addEventListener('mouseup', onMouseUp);
    // Pojistka pro puštění myši mimo okno
    window.addEventListener('mouseleave', onMouseUp);
    window.addEventListener('keydown', onKeyDown);

    // 4. NAČTENÍ MODELŮ
    loadModels();
    
    // 5. Event listener pro tlačítko spawn testovacích itemů
    setTimeout(() => {
        const spawnItemBtn = document.getElementById('spawn-item-btn');
        if (spawnItemBtn) {
            spawnItemBtn.addEventListener('click', () => {
                const select = document.getElementById('spawn-item-select');
                const selectedItem = select ? select.value : 'injector';
                
                switch(selectedItem) {
                    case 'injector':
                        spawnInjector();
                        break;
                    case 'tester':
                        spawnTester();
                        break;
                    case 'pliers':
                        spawnPliers();
                        break;
                    case 'tooth':
                        spawnTooth();
                        break;
                    case 'candy':
                        spawnCandy();
                        break;
                    case 'brain':
                        spawnBrain();
                        break;
                    case 'leech':
                        spawnLeech();
                        break;
                    case 'hammer':
                        spawnHammer();
                        break;
                    case 'hearth':
                        spawnHearth();
                        break;
                }
            });
        }
    }, 100);
    
    // Nastavit náhodné číslo pro player ID
    const playerIdNumber = Math.floor(Math.random() * 10000); // 0-9999
    const playerIdElement = document.getElementById('player-id-number');
    if (playerIdElement) {
        playerIdElement.textContent = String(playerIdNumber).padStart(4, '0');
    }
    
    // 6. Inicializovat UI (toxikace začíná na 0)
    updateUI();
}

function createEnvironment() {
    // Stůl rozdělený na dvě poloviny (levou a pravou) - rozdělí se uprostřed a padnou dolů
    const tableThickness = 0.2;
    const tableWidth = 10;
    const tableDepth = 6;
    const halfWidth = tableWidth / 2; // Šířka každé poloviny
    
    // Načíst texturu dřeva - PS1 HORROR STYL (trash rozlišení)
    const textureLoader = new THREE.TextureLoader();
    const woodTexture = textureLoader.load('models/textures/wood_table.jpg', (texture) => {
        // Po načtení textury aplikovat PS1 styl
        texture.wrapS = THREE.RepeatWrapping;
        texture.wrapT = THREE.RepeatWrapping;
        texture.repeat.set(1, 1);
        
        // Snížit texturu na trash quality (64x64)
        const ps1Texture = downscaleTexture(texture, 64);
        
        // Vytvořit materiál s PS1 texturou a flat shading
        const tableMat = new THREE.MeshLambertMaterial({
            map: ps1Texture,
            flatShading: true, // Flat shading pro PS1 efekt
            side: THREE.DoubleSide, // Renderovat z obou stran, aby stůl byl viditelný i při otáčení
            depthWrite: true, // Zapisovat do depth bufferu
            depthTest: true // Použít depth test
        });
        
        // Aplikovat PS1 styl na geometrii stolu (vertex snapping)
        snapVertices(leftGeo, 0.2);
        snapVertices(rightGeo, 0.2);
        
        tableLeftMesh.material = tableMat;
        const clonedTableMat = tableMat.clone();
        clonedTableMat.side = THREE.DoubleSide; // Ujistit se, že clone má také DoubleSide
        tableRightMesh.material = clonedTableMat;
    });
    
    // Dočasný materiál během načítání
    const tempTableMat = new THREE.MeshLambertMaterial({ 
        color: 0x8B4513, 
        flatShading: true,
        side: THREE.DoubleSide, // Renderovat z obou stran
        depthWrite: true, // Zapisovat do depth bufferu - stůl musí zapisovat
        depthTest: true // Použít depth test
    });
    
    // Levá polovina stolu - PS1 STYL
    const leftGeo = new THREE.BoxGeometry(halfWidth, tableThickness, tableDepth);
    tableLeftMesh = new THREE.Mesh(leftGeo, tempTableMat);
    tableLeftMesh.position.set(-halfWidth/2, -0.1, 0);
    tableLeftMesh.receiveShadow = false;
    tableLeftMesh.frustumCulled = false; // Vypnout frustum culling, aby stůl nezmizel při otáčení
    tableLeftMesh.renderOrder = 10; // Vyšší priorita - renderovat jako poslední (nad podlahou a ostatními objekty)
    tableLeftMesh.userData.isPS1Table = true; // Flag pro wobble efekt
    scene.add(tableLeftMesh);
    
    // Pravá polovina stolu - PS1 STYL
    const rightGeo = new THREE.BoxGeometry(halfWidth, tableThickness, tableDepth);
    tableRightMesh = new THREE.Mesh(rightGeo, tempTableMat.clone());
    tableRightMesh.position.set(halfWidth/2, -0.1, 0);
    tableRightMesh.receiveShadow = false;
    tableRightMesh.frustumCulled = false; // Vypnout frustum culling, aby stůl nezmizel při otáčení
    tableRightMesh.renderOrder = 10; // Vyšší priorita - renderovat jako poslední (nad podlahou a ostatními objekty)
    tableRightMesh.userData.isPS1Table = true; // Flag pro wobble efekt
    scene.add(tableRightMesh);

    // Stůl (Fyzika) - Hluboký blok (pro kolize, stůl je statický dokud se neotevře)
    const tableShapeLeft = new CANNON.Box(new CANNON.Vec3(halfWidth/2, 5, 3)); 
    tableLeftBody = new CANNON.Body({
        mass: 0,
        position: new CANNON.Vec3(-halfWidth/2, -5, 0),
        material: world.defaultMaterial
    });
    tableLeftBody.addShape(tableShapeLeft);
    world.addBody(tableLeftBody);
    
    const tableShapeRight = new CANNON.Box(new CANNON.Vec3(halfWidth/2, 5, 3));
    tableRightBody = new CANNON.Body({
        mass: 0,
        position: new CANNON.Vec3(halfWidth/2, -5, 0),
        material: world.defaultMaterial
    });
    tableRightBody.addShape(tableShapeRight);
    world.addBody(tableRightBody);

    // PODLAHA - Černá, PS1 HORROR STYL
    const floorSize = 20;
    const floorThickness = 0.2;
    const floorGeo = new THREE.BoxGeometry(floorSize, floorThickness, floorSize);
    
    // Černý materiál pro podlahu
    const floorMat = new THREE.MeshLambertMaterial({ 
        color: 0x000000, // Černá barva
        flatShading: true,
        depthWrite: false, // NEZAPISOVAT do depth bufferu - aby neblokovala stůl
        depthTest: true // Použít depth test pro správné renderování
    });
    
    floorMesh = new THREE.Mesh(floorGeo, floorMat);
    floorMesh.position.set(0, -0.5, 0); // Pod stolem (stůl je na Y=-0.1)
    floorMesh.receiveShadow = false;
    floorMesh.renderOrder = -10; // Nižší priorita - renderovat jako první (pod stolem)
    
    // Aplikovat PS1 styl na podlahu
    snapVertices(floorGeo, 0.3);
    floorMesh.userData.isPS1Floor = true;
    scene.add(floorMesh);
    
    // Fyzika podlahy
    const floorBody = new CANNON.Body({
        mass: 0,
        position: new CANNON.Vec3(0, -0.5 - floorThickness/2, 0),
        material: world.defaultMaterial
    });
    floorBody.addShape(new CANNON.Box(new CANNON.Vec3(floorSize/2, floorThickness/2, floorSize/2)));
    world.addBody(floorBody);

    // Neviditelné stěny
    const wallThickness = 1;
    const wallHeight = 5;
    const walls = [
        { pos: [0, 1, -3 - wallThickness], size: [6, wallHeight, wallThickness] },
        { pos: [0, 1, 3 + wallThickness], size: [6, wallHeight, wallThickness] },
        { pos: [-5 - wallThickness, 1, 0], size: [wallThickness, wallHeight, 4] },
        { pos: [5 + wallThickness, 1, 0], size: [wallThickness, wallHeight, 4] }
    ];
    walls.forEach(w => {
        const wallBody = new CANNON.Body({ mass: 0, position: new CANNON.Vec3(...w.pos), material: world.defaultMaterial });
        wallBody.addShape(new CANNON.Box(new CANNON.Vec3(...w.size)));
        world.addBody(wallBody);
    });

    // Rovina pro myš (pro raycasting při dragu) - v rovině Z=0 (nebo kolmo na kameru)
    // Vytvoříme ji virtuálně v onMouseMove
}

// --- PS1 HORROR STYL FUNKCE ---

// Funkce pro snížení rozlišení textury (trash quality)
function downscaleTexture(texture, maxSize = 64) {
    if (!texture || !texture.image) return texture;
    
    const img = texture.image;
    if (!img.width) return texture;
    
    const canvas = document.createElement('canvas');
    const ctx = canvas.getContext('2d');
    
    // Vypočítat nové rozlišení (čtvercové, nízké)
    const newSize = Math.min(maxSize, Math.max(32, Math.min(img.width, img.height)));
    canvas.width = newSize;
    canvas.height = newSize;
    
    // Nejbližší soused pro pixelizaci
    ctx.imageSmoothingEnabled = false;
    ctx.drawImage(img, 0, 0, newSize, newSize);
    
    // Přidat šum (noise) pro PS1 efekt
    const imageData = ctx.getImageData(0, 0, newSize, newSize);
    const data = imageData.data;
    
    for (let i = 0; i < data.length; i += 4) {
        // Přidat náhodný šum do každého pixelu
        const noise = (Math.random() - 0.5) * 30; // Šum v rozsahu -15 až +15
        data[i] = Math.max(0, Math.min(255, data[i] + noise));     // R
        data[i + 1] = Math.max(0, Math.min(255, data[i + 1] + noise)); // G
        data[i + 2] = Math.max(0, Math.min(255, data[i + 2] + noise)); // B
    }
    
    ctx.putImageData(imageData, 0, 0);
    
    const newTexture = new THREE.CanvasTexture(canvas);
    newTexture.minFilter = THREE.NearestFilter; // Pixel-perfect
    newTexture.magFilter = THREE.NearestFilter;
    newTexture.generateMipmaps = false;
    newTexture.anisotropy = 1;
    return newTexture;
}

// Vertex snapping pro PS1 efekt (kvantifikace vertexů)
function snapVertices(geometry, snapAmount = 0.1) {
    if (!geometry || !geometry.attributes || !geometry.attributes.position) return;
    const positions = geometry.attributes.position;
    for (let i = 0; i < positions.count; i++) {
        positions.setX(i, Math.round(positions.getX(i) / snapAmount) * snapAmount);
        positions.setY(i, Math.round(positions.getY(i) / snapAmount) * snapAmount);
        positions.setZ(i, Math.round(positions.getZ(i) / snapAmount) * snapAmount);
    }
    positions.needsUpdate = true;
    if (geometry.computeVertexNormals) {
        geometry.computeVertexNormals();
    }
}

// Aplikovat PS1 styl na mesh (flat shading, vertex snapping, low-res textury)
function applyPS1Style(mesh, snapAmount = 0.1, textureSize = 64) {
    if (!mesh || !mesh.geometry) return;
    
    // Vertex snapping
    snapVertices(mesh.geometry, snapAmount);
    
    // Flat shading - použít computeVertexNormals pouze pokud metoda existuje
    if (mesh.geometry && typeof mesh.geometry.computeVertexNormals === 'function') {
        try {
            mesh.geometry.computeVertexNormals();
        } catch (e) {
            console.warn('Failed to compute vertex normals:', e);
        }
    }
    
    // Upravit materiál
    if (mesh.material) {
        const materials = Array.isArray(mesh.material) ? mesh.material : [mesh.material];
        materials.forEach(mat => {
            // Flat shading
            if (mat.flatShading !== undefined) {
                mat.flatShading = true;
            }
            
            // Snížit rozlišení textur
            if (mat.map) {
                mat.map = downscaleTexture(mat.map, textureSize);
            }
            
            // Zjednodušit materiál
            mat.needsUpdate = true;
        });
    }
}

// Wobble efekt pro PS1 horor (vertex wobble)
function applyWobbleEffect(mesh, intensity = 0.02) {
    if (!mesh.geometry || !mesh.geometry.attributes.position) return;
    
    const positions = mesh.geometry.attributes.position;
    const originalPositions = mesh.userData.originalPositions || [];
    
    // Uložit původní pozice poprvé
    if (originalPositions.length === 0) {
        for (let i = 0; i < positions.count; i++) {
            originalPositions.push({
                x: positions.getX(i),
                y: positions.getY(i),
                z: positions.getZ(i)
            });
        }
        mesh.userData.originalPositions = originalPositions;
    }
    
    // Aplikovat wobble
    wobbleTime += 0.016; // ~60fps
    for (let i = 0; i < positions.count; i++) {
        const orig = originalPositions[i];
        const wobbleX = Math.sin(wobbleTime * 2 + orig.x * 10) * intensity;
        const wobbleY = Math.cos(wobbleTime * 3 + orig.y * 10) * intensity;
        const wobbleZ = Math.sin(wobbleTime * 1.5 + orig.z * 10) * intensity;
        
        positions.setX(i, orig.x + wobbleX);
        positions.setY(i, orig.y + wobbleY);
        positions.setZ(i, orig.z + wobbleZ);
    }
    
    positions.needsUpdate = true;
    if (mesh.geometry && mesh.geometry.computeVertexNormals) {
        mesh.geometry.computeVertexNormals();
    }
}

// Nová funkce pro normalizaci velikosti
function normalizeAndCenterModel(model, targetSize) {
    const group = new THREE.Group();
    
    model.scale.set(1, 1, 1);
    model.position.set(0, 0, 0);
    model.rotation.set(0, 0, 0);
    
    const box = new THREE.Box3().setFromObject(model);
    const size = box.getSize(new THREE.Vector3());
    const maxDim = Math.max(size.x, size.y, size.z);
    
    const scaleFactor = targetSize / maxDim;
    model.scale.set(scaleFactor, scaleFactor, scaleFactor);
    
    const center = box.getCenter(new THREE.Vector3()).multiplyScalar(scaleFactor);
    model.position.sub(center);
    
    model.traverse(c => {
        if(c.isMesh) {
            c.castShadow = false; // Vypnout stíny pro výkon
            c.receiveShadow = false; // Vypnout stíny pro výkon
            if(!c.material.map && (!c.material.color || c.material.color.getHex() === 0)) {
                 c.material = new THREE.MeshLambertMaterial({color: 0xcccccc}); // Jednodušší materiál
            } else if (c.material.isMeshStandardMaterial) {
                // Převést StandardMaterial na jednodušší LambertMaterial
                const oldMat = c.material;
                c.material = new THREE.MeshLambertMaterial({
                    color: oldMat.color,
                    map: oldMat.map,
                    transparent: oldMat.transparent,
                    opacity: oldMat.opacity
                });
            }
        }
    });

    group.add(model);
    const finalSize = size.clone().multiplyScalar(scaleFactor);
    return { group, boxSize: finalSize };
}

// --- TRACKER FUNKCE ---

// Vytvoří tracker texture s HP a toxicitu
function createTrackerTexture(baseTexture, hp, toxicity, isPlayer = true) {
    const canvas = document.createElement('canvas');
    canvas.width = baseTexture && baseTexture.image ? baseTexture.image.width : 512;
    canvas.height = baseTexture && baseTexture.image ? baseTexture.image.height : 256;
    const ctx = canvas.getContext('2d');
    
    // Nakreslit základní texturu tracker.png nebo vytvořit pozadí
    if (baseTexture && baseTexture.image) {
        ctx.drawImage(baseTexture.image, 0, 0, canvas.width, canvas.height);
    } else {
        // Vytvořit tmavé pozadí pro tracker (pokud tracker.png neexistuje)
        ctx.fillStyle = '#1a1a1a';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        // Rámeček
        ctx.strokeStyle = '#444444';
        ctx.lineWidth = 4;
        ctx.strokeRect(10, 10, canvas.width - 20, canvas.height - 20);
    }
    
    // Vycentrovat srdíčka - 5 slotů v jedné řádce, vycentrované
    const heartSize = 42; // Větší srdíčka
    const heartSpacing = 45;
    const totalHeartsWidth = (5 - 1) * heartSpacing; // Šířka všech srdíček včetně mezer
    const heartStartX = (canvas.width - totalHeartsWidth) / 2; // Vycentrovat
    const heartY = canvas.height * 0.4; // Střed trackeru
    
    for (let i = 0; i < 5; i++) {
        const heartX = heartStartX + i * heartSpacing;
        if (i < hp) {
            // Plné srdíčko
            ctx.fillStyle = '#ff4444';
            drawHeart(ctx, heartX, heartY, heartSize);
        } else {
            // Prázdné srdíčko (outline)
            ctx.strokeStyle = '#666666';
            ctx.lineWidth = 2;
            drawHeartOutline(ctx, heartX, heartY, heartSize);
        }
    }
    
    // Toxicita - bar vycentrovaný pod srdíčky
    const barWidth = canvas.width * 0.75; // Větší šířka pro lepší využití prostoru
    const barHeight = 18;
    const barX = (canvas.width - barWidth) / 2; // Vycentrovat
    const barY = canvas.height * 0.65; // Pod srdíčky
    
    // Bar pozadí (šedá)
    ctx.fillStyle = '#333333';
    ctx.fillRect(barX, barY, barWidth, barHeight);
    
    // Bar toxicity (zelená/žlutá/oranžová/červená podle úrovně)
    const toxicityWidth = (toxicity / 5) * barWidth;
    let toxicityColor = '#00ff00'; // Zelená
    if (toxicity >= 4) toxicityColor = '#ff0000'; // Červená
    else if (toxicity >= 3) toxicityColor = '#ff6600'; // Oranžová
    else if (toxicity >= 2) toxicityColor = '#ffaa00'; // Žlutooranžová
    else if (toxicity >= 1) toxicityColor = '#ffff00'; // Žlutá
    
    ctx.fillStyle = toxicityColor;
    ctx.fillRect(barX, barY, toxicityWidth, barHeight);
    
    // Text "Toxicity" - menší, nad barem
    ctx.fillStyle = '#ffffff';
    ctx.font = 'bold 16px Arial';
    const textWidth = ctx.measureText('Toxicity').width;
    ctx.fillText('Toxicity', (canvas.width - textWidth) / 2, barY - 8);
    
    const texture = new THREE.CanvasTexture(canvas);
    texture.needsUpdate = true;
    // PS1 styl - pixelizace
    texture.minFilter = THREE.NearestFilter;
    texture.magFilter = THREE.NearestFilter;
    texture.generateMipmaps = false;
    
    return texture;
}

// Pomocná funkce pro nakreslení srdíčka
function drawHeart(ctx, x, y, size) {
    ctx.save();
    ctx.translate(x, y);
    ctx.beginPath();
    ctx.moveTo(0, size * 0.3);
    ctx.bezierCurveTo(0, 0, -size * 0.5, 0, -size * 0.5, size * 0.3);
    ctx.bezierCurveTo(-size * 0.5, size * 0.5, 0, size * 0.7, 0, size);
    ctx.bezierCurveTo(0, size * 0.7, size * 0.5, size * 0.5, size * 0.5, size * 0.3);
    ctx.bezierCurveTo(size * 0.5, 0, 0, 0, 0, size * 0.3);
    ctx.fill();
    ctx.restore();
}

// Pomocná funkce pro nakreslení obrysu srdíčka
function drawHeartOutline(ctx, x, y, size) {
    ctx.save();
    ctx.translate(x, y);
    ctx.beginPath();
    ctx.moveTo(0, size * 0.3);
    ctx.bezierCurveTo(0, 0, -size * 0.5, 0, -size * 0.5, size * 0.3);
    ctx.bezierCurveTo(-size * 0.5, size * 0.5, 0, size * 0.7, 0, size);
    ctx.bezierCurveTo(0, size * 0.7, size * 0.5, size * 0.5, size * 0.5, size * 0.3);
    ctx.bezierCurveTo(size * 0.5, 0, 0, 0, 0, size * 0.3);
    ctx.stroke();
    ctx.restore();
}

// Vytvoří tracker mesh
function createTrackerMesh(position, rotation, isPlayer = true) {
    // Tracker je plochý box, lehce vysoký
    const trackerWidth = 2.0;  // Šířka
    const trackerHeight = 0.1; // Výška (lehce vysoký)
    const trackerDepth = 1.0;  // Hloubka
    
    const trackerGeo = new THREE.BoxGeometry(trackerWidth, trackerHeight, trackerDepth);
    
    // Dočasný materiál, textura se načte později
    const tempMat = new THREE.MeshLambertMaterial({ color: 0x222222, flatShading: true });
    
    const trackerMesh = new THREE.Mesh(trackerGeo, tempMat);
    trackerMesh.position.set(position.x, position.y, position.z);
    trackerMesh.rotation.set(rotation.x, rotation.y, rotation.z);
    trackerMesh.receiveShadow = false;
    trackerMesh.frustumCulled = false; // Vypnout frustum culling - tracker musí být vždy viditelný
    trackerMesh.renderOrder = 20; // Vyšší než stůl (10) - renderovat jako úplně poslední (nad vším)
    
    // PS1 styl - vertex snapping
    snapVertices(trackerGeo, 0.05);
    
    return trackerMesh;
}

function loadModels() {
    const loader = new FBXLoader();
    
    // Helper pro error
    const onError = (err) => {
        console.error(err);
        showStatus("CHYBA NAČÍTÁNÍ MODELU: " + err.message, true);
    };

    // 1. Pill
    loader.load('models/pill/pill.fbx', (obj) => {
        pillModel = obj;
        updateLoadingProgress('Pill');
    }, undefined, onError);
    
    // 2. Pill Tablet (OBJ soubor)
    const objLoader = new OBJLoader();
    objLoader.load('models/pilltablet/Pill.obj', (obj) => {
        pillTabletModel = obj;
        updateLoadingProgress('Pill Tablet');
    }, undefined, onError);
    
    // 3. Vitamin Pill (OBJ soubor) - pro třetí kolo
    objLoader.load('models/Vitamin pill/16893_Vitamin_pill_v1_NEW.obj', (obj) => {
        vitaminPillModel = obj;
        updateLoadingProgress('Vitamin Pill');
    }, undefined, onError);

    // 4. Bottle - Načteme, ale nepřidáme hned do scény
    loader.load('models/Simple Pill Bottle/Bottle.fbx', (obj) => {
        try {
            // Zvětšíme lahev podle debug hodnoty
            const { group, boxSize } = normalizeAndCenterModel(obj, bottleCapScale);
            group.name = "BottleGroup"; 
            
            bottleModelData = { group, boxSize };
            updateLoadingProgress('Bottle');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 5. Zombie oponent - Načteme a umístíme naproti hráči - PS1 HORROR STYL
    loader.load('models/zombie/source/Male_Zombie.fbx', (obj) => {
        try {
            // PS1 HORROR STYL: Aplikovat low-poly, noisy, wobbly, trash rozlišení
            obj.traverse((child) => {
                if (child.isMesh) {
                    // Vypnout stíny pro zombie
                    child.castShadow = false;
                    child.receiveShadow = false;
                    
                    // Aplikovat PS1 styl
                    applyPS1Style(child, 0.15, 64); // Vertex snap 0.15, textura 64x64
                    
                    // Zjednodušit materiály - PS1 styl
                    if (child.material) {
                        const materials = Array.isArray(child.material) ? child.material : [child.material];
                        materials.forEach(mat => {
                            // Flat shading pro PS1 efekt
                            mat.flatShading = true;
                            
                            // Vypnout všechny mapy
                            mat.normalMap = null;
                            mat.envMap = null;
                            mat.aoMap = null;
                            mat.roughnessMap = null;
                            mat.metalnessMap = null;
                            
                            // Snížit rozlišení textur na trash quality
                            if (mat.map) {
                                mat.map = downscaleTexture(mat.map, 64);
                            }
                            
                            // Zjednodušit materiál na MeshLambertMaterial
                            if (mat.isMeshStandardMaterial || mat.isMeshPhongMaterial) {
                                const newMat = new THREE.MeshLambertMaterial({
                                    color: mat.color,
                                    map: mat.map,
                                    transparent: mat.transparent,
                                    opacity: mat.opacity,
                                    depthWrite: true, // Zapisovat do depth bufferu
                                    depthTest: true // Použít depth test
                                });
                                newMat.flatShading = true;
                                if (Array.isArray(child.material)) {
                                    const idx = child.material.indexOf(mat);
                                    child.material[idx] = newMat;
                                } else {
                                    child.material = newMat;
                                }
                            } else {
                                // Ujistit se, že všechny materiály mají správné depth testování
                                mat.depthWrite = true;
                                mat.depthTest = true;
                            }
                        });
                    }
                }
            });
            
            // Normalizovat a vycentrovat zombie model (velikost ~2 jednotky na výšku)
            const { group, boxSize } = normalizeAndCenterModel(obj, 2.0);
            group.name = "ZombieGroup";
            
            // OPTIMALIZACE: Vypnout frustum culling pro zombie (je vždy viditelný)
            group.frustumCulled = false;
            
            // Umístit zombie na opačné straně stolu (naproti hráči)
            // Použijeme debug hodnoty, pokud jsou nastaveny
            group.position.set(zombieDebugPos.x, zombieDebugPos.y, zombieDebugPos.z);
            group.rotation.set(zombieDebugRot.x, zombieDebugRot.y, zombieDebugRot.z);
            group.scale.set(zombieDebugScale, zombieDebugScale, zombieDebugScale);
            
            // Zkusit najít kostru a upravit pozici, aby seděl (ne T-pose)
            // Projdeme všechny děti a hledáme kosti (skelton hierarchy)
            obj.traverse((child) => {
                // Zkusit najít kosti podle jména a upravit jejich rotaci pro sedící pozici
                const nameLower = child.name.toLowerCase();
                
                // Kolena: ohnout dolů (sedící pozice)
                if (nameLower.includes('thigh') || nameLower.includes('upperleg') || nameLower.includes('leg') && nameLower.includes('upper')) {
                    if (child.rotation) {
                        child.rotation.x = -Math.PI / 2.2; // Ohnout kolena pro sed
                    }
                }
                // Dolní část nohy: ohnout
                if (nameLower.includes('knee') || nameLower.includes('lowerleg') || nameLower.includes('leg') && nameLower.includes('lower')) {
                    if (child.rotation) {
                        child.rotation.x = Math.PI / 2.8; // Ohnout dolní část nohy
                    }
                }
                // Paže: snížit z T-pose dolů k tělu
                if (nameLower.includes('upperarm') || nameLower.includes('shoulder')) {
                    if (child.rotation) {
                        child.rotation.x = Math.PI / 4; // Snížit paže z T-pose
                        child.rotation.z = -Math.PI / 10; // Přiblížit k tělu
                    }
                }
                // Lokty: mírně ohnout
                if (nameLower.includes('forearm') || nameLower.includes('lowerarm')) {
                    if (child.rotation) {
                        child.rotation.x = -Math.PI / 5; // Ohnout lokty
                    }
                }
            });
            
            // Animace pro zombie
            if (obj.animations && obj.animations.length > 0) {
                // Vytvořit AnimationMixer pro přehrávání animací
                zombieMixer = new THREE.AnimationMixer(group);
                
                // Zkusit najít sitting nebo idle animaci
                let sittingAnim = obj.animations.find(anim => 
                    anim.name.toLowerCase().includes('sit') || 
                    anim.name.toLowerCase().includes('idle')
                );
                
                // Pokud není sitting, použít první dostupnou
                if (!sittingAnim && obj.animations.length > 0) {
                    sittingAnim = obj.animations[0];
                }
                
                if (sittingAnim) {
                    const action = zombieMixer.clipAction(sittingAnim);
                    action.play();
                }
            }
            
            zombieGroup = group;
            zombieGroup.renderOrder = 0; // Nižší priorita než stůl (10) - renderovat před stolem
            scene.add(zombieGroup);
            updateLoadingProgress('Zombie');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 6. Injector - Načteme, ale nepřidáme hned do scény
    loader.load('models/injector/Morhpine Auto Injector.fbx', (obj) => {
        try {
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0);
            group.name = "InjectorGroup";
            
            // Aplikovat PS1 styl na injector
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                }
            });
            
            injectorModelData = { group, boxSize };
            updateLoadingProgress('Injector');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 7. Tester (Medkit) - Načteme, ale nepřidáme hned do scény
    loader.load('models/tester/Medkit1_low.fbx', (obj) => {
        try {
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0);
            group.name = "TesterGroup";
            
            // Aplikovat PS1 styl na tester
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                }
            });
            
            testerModelData = { group, boxSize };
            updateLoadingProgress('Tester');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 8. Kleště - Načteme, ale nepřidáme hned do scény
    loader.load('models/kleste/kleste.FBX', (obj) => {
        try {
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0);
            group.name = "PliersGroup";
            
            // Aplikovat PS1 styl na kleště
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                }
            });
            
            pliersModelData = { group, boxSize };
            updateLoadingProgress('Pliers');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 9. Zub - Načteme, ale nepřidáme hned do scény (3x menší)
    loader.load('models/zub/dent.fbx', (obj) => {
        try {
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0 / 3.0);
            group.name = "ToothGroup";
            
            // Aplikovat PS1 styl na zub
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                }
            });
            
            toothModelData = { group, boxSize };
            updateLoadingProgress('Tooth');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 10. Candy - Načteme, ale nepřidáme hned do scény
    loader.load('models/candy/untitled.fbx', (obj) => {
        try {
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0);
            group.name = "CandyGroup";
            
            // Aplikovat PS1 styl na candy
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                }
            });
            
            candyModelData = { group, boxSize };
            updateLoadingProgress('Candy');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 11. Brain - Načteme, ale nepřidáme hned do scény (GLB soubor)
    const gltfLoader = new GLTFLoader();
    gltfLoader.load('models/brain/Rotten Brain.glb', (gltf) => {
        try {
            const obj = gltf.scene;
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0);
            group.name = "BrainGroup";
            
            // Aplikovat PS1 styl na brain a nastavit barvu reálného mozku
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                    
                    // Nastavit barvu reálného mozku (růžovo-šedá)
                    if (child.material) {
                        const materials = Array.isArray(child.material) ? child.material : [child.material];
                        materials.forEach(mat => {
                            // Barva reálného mozku: světle růžovo-šedá (#E6B3B3 nebo podobná)
                            const brainColor = new THREE.Color(0xE6B3B3); // Růžovo-šedá barva mozku
                            
                            // Vytvořit nový materiál s barvou mozku
                            const newMat = new THREE.MeshLambertMaterial({
                                color: brainColor,
                                flatShading: true,
                                depthWrite: true,
                                depthTest: true
                            });
                            
                            if (Array.isArray(child.material)) {
                                const idx = child.material.indexOf(mat);
                                child.material[idx] = newMat;
                            } else {
                                child.material = newMat;
                            }
                        });
                    }
                }
            });
            
            brainModelData = { group, boxSize };
            updateLoadingProgress('Brain');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 12. Leech - Načteme, ale nepřidáme hned do scény
    loader.load('models/leech/Leech.fbx', (obj) => {
        try {
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0);
            group.name = "LeechGroup";
            
            // Aplikovat PS1 styl na leech
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                }
            });
            
            leechModelData = { group, boxSize };
            updateLoadingProgress('Leech');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 13. Hammer - Načteme, ale nepřidáme hned do scény
    loader.load('models/hammer/mjolnir_low.fbx', (obj) => {
        try {
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0);
            group.name = "HammerGroup";
            
            // Aplikovat PS1 styl na hammer
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                }
            });
            
            hammerModelData = { group, boxSize };
            updateLoadingProgress('Hammer');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);

    // 14. Hearth - Načteme, ale nepřidáme hned do scény
    loader.load('models/hearth/Heart.fbx', (obj) => {
        try {
            const { group, boxSize } = normalizeAndCenterModel(obj, 1.0);
            group.name = "HearthGroup";
            
            // Aplikovat PS1 styl na hearth
            group.traverse((child) => {
                if (child.isMesh) {
                    applyPS1Style(child, 0.1, 64);
                    child.castShadow = false;
                    child.receiveShadow = false;
                }
            });
            
            hearthModelData = { group, boxSize };
            updateLoadingProgress('Hearth');
        } catch (e) {
            onError(e);
        }
    }, undefined, onError);
    
    // 15. Načíst tracker texturu
    const textureLoader = new THREE.TextureLoader();
    textureLoader.load(
        'models/textures/tracker.png', 
        (texture) => {
            // Aplikovat PS1 styl na texturu
            trackerBaseTexture = downscaleTexture(texture, 128);
            updateLoadingProgress('Tracker Texture');
            
            // Vytvořit trackery po načtení textury
            createTrackers();
            updateUI(); // Aktualizovat UI po vytvoření trackerů
        }, 
        undefined, 
        (err) => {
            console.warn('Tracker.png nenalezen, vytvářím trackery bez základní textury:', err);
            // Nastavit trackerBaseTexture na null - tracker bude fungovat i bez základní textury
            trackerBaseTexture = null;
            updateLoadingProgress('Tracker Texture');
            
            // Vytvořit trackery i bez základní textury
            createTrackers();
            updateUI(); // Aktualizovat UI po vytvoření trackerů
        }
    );
}

// Vytvoří tracker meshy pro hráče a oponenta
function createTrackers() {
    // Trackery lze vytvořit i bez základní textury (pouze s HP a toxicity)
    
    // Tracker pro hráče (blíž ke kameře, pozitivní Z)
    // tableRightMesh je na (2.5, -0.1, 0), tracker má být na (0, 0.05, 2.5)
    // Relativní pozice k tableRightMesh: (0-2.5, 0.05-(-0.1), 2.5-0) = (-2.5, 0.15, 2.5)
    const playerPos = { x: -2.5, y: 0.15, z: 2.5 }; // Relativní pozice k pravé polovině stolu
    const playerRot = { x: 0, y: 0, z: 0 };
    playerTrackerMesh = createTrackerMesh(playerPos, playerRot, true);
    
    // Vytvořit dynamickou texturu pro hráče
    playerTrackerTexture = createTrackerTexture(trackerBaseTexture, playerHP, playerToxicity, true);
    playerTrackerMesh.material = new THREE.MeshLambertMaterial({ 
        map: playerTrackerTexture, 
        flatShading: true,
        depthWrite: true, // Zapisovat do depth bufferu
        depthTest: true // Použít depth test
    });
    
    // Přidat tracker jako potomek pravé poloviny stolu (aby se pohyboval se stolem)
    if (tableRightMesh) {
        tableRightMesh.add(playerTrackerMesh);
    } else {
        scene.add(playerTrackerMesh);
    }
    
    // Tracker pro oponenta (dál od kamery, negativní Z)
    // tableLeftMesh je na (-2.5, -0.1, 0), tracker má být na (0, 0.05, -2.5)
    // Relativní pozice k tableLeftMesh: (0-(-2.5), 0.05-(-0.1), -2.5-0) = (2.5, 0.15, -2.5)
    const enemyPos = { x: 2.5, y: 0.15, z: -2.5 }; // Relativní pozice k levé polovině stolu
    const enemyRot = { x: 0, y: Math.PI, z: 0 }; // Otočený k oponentovi
    enemyTrackerMesh = createTrackerMesh(enemyPos, enemyRot, false);
    
    // Vytvořit dynamickou texturu pro oponenta
    enemyTrackerTexture = createTrackerTexture(trackerBaseTexture, enemyHP, enemyToxicity, false);
    enemyTrackerMesh.material = new THREE.MeshLambertMaterial({ 
        map: enemyTrackerTexture, 
        flatShading: true,
        depthWrite: true, // Zapisovat do depth bufferu
        depthTest: true // Použít depth test
    });
    
    // Přidat tracker jako potomek levé poloviny stolu (aby se pohyboval se stolem)
    if (tableLeftMesh) {
        tableLeftMesh.add(enemyTrackerMesh);
    } else {
        scene.add(enemyTrackerMesh);
    }
}

let capConstraint; // Vazba víčka

function spawnBottle() {
    if (!bottleModelData) return;
    const { group, boxSize } = bottleModelData;
    
    bottleGroup = group;
    scene.add(bottleGroup);

    // --- FYZIKA: DUTÁ LAHEV (Compound Shape) ---
    // Potřebujeme, aby v ní mohly být pilulky.
    // Skládáme z:
    // 1. Dno (Cylinder/Box)
    // 2. Stěny (8 Boxů dokola)
    
    // Spawnovat lahev přímo nad středem stolu, aby padla doprostřed
    // Stůl je na (0, 0, 0) - střed stolu
    // Spawnujeme lahev přímo nad středem (X=0, Z=0), nižší výška pro rychlejší pád
    const spawnX = 0; // Přímo nad středem stolu
    const spawnY = 5; // Nižší výška (rychlejší pád, místo 12)
    const spawnZ = 0; // Přímo nad středem stolu
    
    bottleBody = new CANNON.Body({
        mass: 2, 
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    // Lahev bude neviditelná na začátku, aby nebyla vidět při spawnu
    bottleGroup.visible = false;
    
    // Zviditelníme lahev po chvíli (když už padá)
    setTimeout(() => {
        if (bottleGroup) {
            bottleGroup.visible = true;
        }
    }, 200); // 200ms zpoždění

    const r = Math.max(boxSize.x, boxSize.z) / 2;
    const h = boxSize.y;
    const wallThickness = 0.05; // Tlustší stěny
    const bottomThickness = 0.1; // Tlustší dno

    // 1. Dno
    // Pozice dna je -h/2 + tloušťka/2
    const bottomShape = new CANNON.Cylinder(r, r, bottomThickness, 16);
    const qBottom = new CANNON.Quaternion();
    qBottom.setFromAxisAngle(new CANNON.Vec3(1,0,0), -Math.PI/2);
    bottleBody.addShape(bottomShape, new CANNON.Vec3(0, -h/2 + bottomThickness/2, 0), qBottom);

    // 2. Stěny (16 segmentů pro kulatější tvar a tlustší stěny)
    const numSegments = 16;
    // const wallThickness = 0.2; // ZDE BYLA CHYBA - už je definováno nahoře. Přenastavíme jen hodnotu? Ne, je to const.
    // Takže nahoře (ř. 251) to musíme změnit na let nebo to tady smazat a použít jiný název.
    // Nejlepší bude použít jiný název pro tuto lokální tloušťku stěny, protože ta nahoře byla pro "default".
    // Ale chceme tlusté stěny (0.2).
    
    const heavyWallThickness = 0.05; // Ještě tenčí stěny
    const innerRadius = r * 0.95; // Ještě větší vnitřní prostor
    
    const segmentWidth = (2 * Math.PI * innerRadius) / numSegments * 1.1; 
    const segmentHeight = h - bottomThickness;
    
    const wallDist = innerRadius + heavyWallThickness/2;

    for(let i=0; i<numSegments; i++) {
        const angle = (i / numSegments) * Math.PI * 2;
        const x = Math.cos(angle) * wallDist;
        const z = Math.sin(angle) * wallDist;
        
        const wallShape = new CANNON.Box(new CANNON.Vec3(heavyWallThickness/2, segmentHeight/2, segmentWidth/2)); 
        
        const qWall = new CANNON.Quaternion();
        qWall.setFromAxisAngle(new CANNON.Vec3(0,1,0), -angle);
        
        bottleBody.addShape(wallShape, new CANNON.Vec3(x, -h/2 + bottomThickness + segmentHeight/2, z), qWall);
    }

    // 3. VÍČKO (CAP) - PEVNÁ SOUČÁST LAHVE
    const capRadius = r * 1.15; 
    const capHeight = h * 0.2; 
    
    // Vizuál (přidáme do bottleGroup)
    const capGeo = new THREE.CylinderGeometry(capRadius, capRadius, capHeight, 16);
    const capMat = new THREE.MeshLambertMaterial({ color: 0xffaa00 }); // Jednodušší materiál pro výkon
    capMesh = new THREE.Mesh(capGeo, capMat);
    capMesh.castShadow = false; // Vypnout stíny pro výkon
    bottleGroup.add(capMesh);
    capMesh.position.set(0, h/2 + capHeight/2, 0);
    
    // Fyzika (Shape přímo v bottleBody)
    const capShape = new CANNON.Box(new CANNON.Vec3(capRadius, capHeight/2, capRadius));
    // Offset relativně k těžišti tělesa (které je 0,0,0 v lokálních souřadnicích)
    // Těžiště lahve je někde uprostřed, ale my jsme si dno nastavili na -h/2.
    // Takže vrch je h/2.
    const capOffset = new CANNON.Vec3(0, h/2 + capHeight/2 - bottomThickness/2, 0); 
    bottleBody.addShape(capShape, capOffset);
    
    // Uložíme index shapu víčka a rozměry pro pozdější spawn pilulek
    bottleBody.userData = { 
        capShapeIndex: 9,
        bottleRadius: r,
        bottleHeight: h
    };

    world.addBody(bottleBody);
    objectsToUpdate.push({ mesh: bottleGroup, body: bottleBody });

    // PILULKY se NESPAWNUJÍ - počkají na otevření lahve

    isBottleOpen = false;
}

function spawnInjector() {
    if (!injectorModelData) return;
    const { group, boxSize } = injectorModelData;
    
    // Odstranit starý injector, pokud existuje
    if (injectorGroup) {
        scene.remove(injectorGroup);
        injectorGroup = null;
    }
    if (injectorBody) {
        world.removeBody(injectorBody);
        const idx = objectsToUpdate.findIndex(o => o.body === injectorBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        injectorBody = null;
    }
    
    // Klonovat skupinu pro nový injector
    injectorGroup = group.clone();
    injectorGroup.name = "InjectorGroup";
    scene.add(injectorGroup);

    // Spawnovat injector nad středem stolu, aby padl na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const injectorShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    injectorBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    injectorBody.addShape(injectorShape);
    injectorBody.userData = { type: 'injector' };
    
    world.addBody(injectorBody);
    objectsToUpdate.push({ mesh: injectorGroup, body: injectorBody });
}

function spawnTester() {
    if (!testerModelData) return;
    const { group, boxSize } = testerModelData;
    
    // Odstranit starý tester, pokud existuje
    if (testerGroup) {
        scene.remove(testerGroup);
        testerGroup = null;
    }
    if (testerBody) {
        world.removeBody(testerBody);
        const idx = objectsToUpdate.findIndex(o => o.body === testerBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        testerBody = null;
    }
    
    // Klonovat skupinu pro nový tester
    testerGroup = group.clone();
    testerGroup.name = "TesterGroup";
    scene.add(testerGroup);

    // Spawnovat tester nad středem stolu, aby padl na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const testerShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    testerBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    testerBody.addShape(testerShape);
    testerBody.userData = { type: 'tester' };
    
    world.addBody(testerBody);
    objectsToUpdate.push({ mesh: testerGroup, body: testerBody });
}

function spawnPliers() {
    if (!pliersModelData) return;
    const { group, boxSize } = pliersModelData;
    
    // Odstranit staré kleště, pokud existují
    if (pliersGroup) {
        scene.remove(pliersGroup);
        pliersGroup = null;
    }
    if (pliersBody) {
        world.removeBody(pliersBody);
        const idx = objectsToUpdate.findIndex(o => o.body === pliersBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        pliersBody = null;
    }
    
    // Klonovat skupinu pro nové kleště
    pliersGroup = group.clone();
    pliersGroup.name = "PliersGroup";
    scene.add(pliersGroup);

    // Spawnovat kleště nad středem stolu, aby padly na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const pliersShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    pliersBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    pliersBody.addShape(pliersShape);
    pliersBody.userData = { type: 'pliers' };
    
    world.addBody(pliersBody);
    objectsToUpdate.push({ mesh: pliersGroup, body: pliersBody });
}

function spawnTooth() {
    if (!toothModelData) return;
    const { group, boxSize } = toothModelData;
    
    // Odstranit starý zub, pokud existuje
    if (toothGroup) {
        scene.remove(toothGroup);
        toothGroup = null;
    }
    if (toothBody) {
        world.removeBody(toothBody);
        const idx = objectsToUpdate.findIndex(o => o.body === toothBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        toothBody = null;
    }
    
    // Klonovat skupinu pro nový zub
    toothGroup = group.clone();
    toothGroup.name = "ToothGroup";
    scene.add(toothGroup);

    // Spawnovat zub nad středem stolu, aby padl na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const toothShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    toothBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    toothBody.addShape(toothShape);
    toothBody.userData = { type: 'tooth' };
    
    world.addBody(toothBody);
    objectsToUpdate.push({ mesh: toothGroup, body: toothBody });
}

function spawnCandy() {
    if (!candyModelData) return;
    const { group, boxSize } = candyModelData;
    
    // Odstranit staré candy, pokud existuje
    if (candyGroup) {
        scene.remove(candyGroup);
        candyGroup = null;
    }
    if (candyBody) {
        world.removeBody(candyBody);
        const idx = objectsToUpdate.findIndex(o => o.body === candyBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        candyBody = null;
    }
    
    // Klonovat skupinu pro nové candy
    candyGroup = group.clone();
    candyGroup.name = "CandyGroup";
    scene.add(candyGroup);

    // Spawnovat candy nad středem stolu, aby padlo na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const candyShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    candyBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    candyBody.addShape(candyShape);
    candyBody.userData = { type: 'candy' };
    
    world.addBody(candyBody);
    objectsToUpdate.push({ mesh: candyGroup, body: candyBody });
}

function spawnBrain() {
    if (!brainModelData) return;
    const { group, boxSize } = brainModelData;
    
    // Odstranit starý brain, pokud existuje
    if (brainGroup) {
        scene.remove(brainGroup);
        brainGroup = null;
    }
    if (brainBody) {
        world.removeBody(brainBody);
        const idx = objectsToUpdate.findIndex(o => o.body === brainBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        brainBody = null;
    }
    
    // Klonovat skupinu pro nový brain
    brainGroup = group.clone();
    brainGroup.name = "BrainGroup";
    scene.add(brainGroup);

    // Spawnovat brain nad středem stolu, aby padl na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const brainShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    brainBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    brainBody.addShape(brainShape);
    brainBody.userData = { type: 'brain' };
    
    world.addBody(brainBody);
    objectsToUpdate.push({ mesh: brainGroup, body: brainBody });
}

function spawnLeech() {
    if (!leechModelData) return;
    const { group, boxSize } = leechModelData;
    
    // Odstranit starý leech, pokud existuje
    if (leechGroup) {
        scene.remove(leechGroup);
        leechGroup = null;
    }
    if (leechBody) {
        world.removeBody(leechBody);
        const idx = objectsToUpdate.findIndex(o => o.body === leechBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        leechBody = null;
    }
    
    // Klonovat skupinu pro nový leech
    leechGroup = group.clone();
    leechGroup.name = "LeechGroup";
    scene.add(leechGroup);

    // Spawnovat leech nad středem stolu, aby padl na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const leechShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    leechBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    leechBody.addShape(leechShape);
    leechBody.userData = { type: 'leech' };
    
    world.addBody(leechBody);
    objectsToUpdate.push({ mesh: leechGroup, body: leechBody });
}

function spawnHammer() {
    if (!hammerModelData) return;
    const { group, boxSize } = hammerModelData;
    
    // Odstranit starý hammer, pokud existuje
    if (hammerGroup) {
        scene.remove(hammerGroup);
        hammerGroup = null;
    }
    if (hammerBody) {
        world.removeBody(hammerBody);
        const idx = objectsToUpdate.findIndex(o => o.body === hammerBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        hammerBody = null;
    }
    
    // Klonovat skupinu pro nový hammer
    hammerGroup = group.clone();
    hammerGroup.name = "HammerGroup";
    scene.add(hammerGroup);

    // Spawnovat hammer nad středem stolu, aby padl na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const hammerShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    hammerBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    hammerBody.addShape(hammerShape);
    hammerBody.userData = { type: 'hammer' };
    
    world.addBody(hammerBody);
    objectsToUpdate.push({ mesh: hammerGroup, body: hammerBody });
}

function spawnHearth() {
    if (!hearthModelData) return;
    const { group, boxSize } = hearthModelData;
    
    // Odstranit starý hearth, pokud existuje
    if (hearthGroup) {
        scene.remove(hearthGroup);
        hearthGroup = null;
    }
    if (hearthBody) {
        world.removeBody(hearthBody);
        const idx = objectsToUpdate.findIndex(o => o.body === hearthBody);
        if (idx !== -1) objectsToUpdate.splice(idx, 1);
        hearthBody = null;
    }
    
    // Klonovat skupinu pro nový hearth
    hearthGroup = group.clone();
    hearthGroup.name = "HearthGroup";
    scene.add(hearthGroup);

    // Spawnovat hearth nad středem stolu, aby padl na stůl
    const spawnX = 0;
    const spawnY = 5;
    const spawnZ = 0;
    
    // Fyzika - jednoduchý box shape
    const hearthShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    hearthBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    hearthBody.addShape(hearthShape);
    hearthBody.userData = { type: 'hearth' };
    
    world.addBody(hearthBody);
    objectsToUpdate.push({ mesh: hearthGroup, body: hearthBody });
}

let pillSpawnInterval = null; // Pro postupný spawn

// Aplikovat barvu special pill - polovina zelená, polovina tmavě fialová
function applySpecialPillColor(mesh) {
    if (!mesh || !mesh.geometry) return;
    
    const geometry = mesh.geometry;
    const positions = geometry.attributes.position;
    
    if (!positions) return;
    
    // Najít minimální a maximální Z hodnotu pro rozdělení pilulky
    let minZ = Infinity;
    let maxZ = -Infinity;
    for (let i = 0; i < positions.count; i++) {
        const z = positions.getZ(i);
        if (z < minZ) minZ = z;
        if (z > maxZ) maxZ = z;
    }
    const midZ = (minZ + maxZ) / 2;
    
    // Vytvořit vertex colors - polovina zelená, polovina fialová podle Z pozice
    const colors = [];
    const green = new THREE.Color(0x00ff00); // Zelená
    const purple = new THREE.Color(0x4b0082); // Tmavě fialová (#4b0082 = indigo)
    
    for (let i = 0; i < positions.count; i++) {
        const z = positions.getZ(i);
        // První polovina (menší Z) = zelená, druhá polovina (větší Z) = fialová
        if (z <= midZ) {
            colors.push(green.r, green.g, green.b);
        } else {
            colors.push(purple.r, purple.g, purple.b);
        }
    }
    
    geometry.setAttribute('color', new THREE.Float32BufferAttribute(colors, 3));
    
    // Použít vertex colors v materiálu
    if (mesh.material) {
        mesh.material = mesh.material.clone();
        mesh.material.vertexColors = true;
    }
}

function spawnPillsFromBottle(bottleBodyRef, r, h) {
    if (!pillModel) return;
    
    // Resetovat seznam pilulek pro nové kolo
    currentRoundPills = [];
    
    // Určit, kolik pilulek spawnovat podle kola
    // Kolo 1: 4 normální pilulky
    // Kolo 2: 4 normální + 3 pilltablet
    // Kolo 3+: 4 normální + 3 pilltablet + 6 vitamin pills
    // Kolo 4+: + 4 special pills (polovina zelená, polovina fialová)
    const numNormalPills = 4;
    const numPillTablets = roundNumber >= 2 ? 3 : 0;
    const numVitaminPills = roundNumber >= 3 ? 6 : 0;
    const numSpecialPills = roundNumber >= 4 ? 4 : 0;
    const totalPills = numNormalPills + numPillTablets + numVitaminPills + numSpecialPills;
    
    // Náhodně vybrat, která normální pilulka je jedovatá (0-3)
    const poisonIndex = Math.floor(Math.random() * numNormalPills);
    
    // Náhodně vybrat, která pilltablet je jedovatá (0-2)
    const pillTabletPoisonIndex = numPillTablets > 0 ? Math.floor(Math.random() * numPillTablets) : -1;
    
    // Náhodně vybrat, která vitamin pill je jedovatá (0-5)
    const vitaminPoisonIndex = numVitaminPills > 0 ? Math.floor(Math.random() * numVitaminPills) : -1;
    
    // Pro special pills: 4 pilulky, 2 smrtelné, 1 přidá 2 toxicity, 1 přidá 1 život
    // Náhodně vybrat, které 2 special pills jsou smrtelné
    let specialPillPoisonIndices = [];
    let specialPillAdds2ToxIndex = -1;
    let specialPillAddsLifeIndex = -1;
    
    if (numSpecialPills > 0) {
        // Vybrat 2 jedovaté (0-3)
        const indices = [0, 1, 2, 3];
        specialPillPoisonIndices.push(indices.splice(Math.floor(Math.random() * indices.length), 1)[0]);
        specialPillPoisonIndices.push(indices.splice(Math.floor(Math.random() * indices.length), 1)[0]);
        
        // Vybrat 1 pro +2 toxicity (zbytek)
        specialPillAdds2ToxIndex = indices.splice(Math.floor(Math.random() * indices.length), 1)[0];
        
        // Zbytek je pro +1 život
        specialPillAddsLifeIndex = indices[0];
    }
    
    let spawnedCount = 0;
    let normalPillCount = 0;
    let pillTabletCount = 0;
    let vitaminPillCount = 0;
    let specialPillCount = 0;
    
    // Spawnujeme pilulky postupně
    const spawnPill = () => {
        if (spawnedCount >= totalPills) {
            if (pillSpawnInterval) {
                clearInterval(pillSpawnInterval);
                pillSpawnInterval = null;
            }
            updatePillStatsUI(); // Aktualizovat UI po spawnu
            return;
        }
        
        let isVitaminPill = false;
        let isPillTablet = false;
        let isSpecialPill = false;
        let isPoison = false;
        let reducesToxicity = false;
        let addsToxicity = false;
        let adds2Toxicity = false;
        let addsLife = false;
        let modelToUse = null;
        
        // Určit typ pilulky podle pořadí spawnu
        if (spawnedCount < numNormalPills) {
            // Normální pilulka
            isPoison = normalPillCount === poisonIndex;
            modelToUse = pillModel;
            normalPillCount++;
        } else if (spawnedCount < numNormalPills + numPillTablets) {
            // Pill tablet (ve 2. a vyšších kolech)
            isPillTablet = true;
            isPoison = pillTabletCount === pillTabletPoisonIndex;
            reducesToxicity = !isPoison; // Nejedovaté pilltablety redukují toxikaci
            modelToUse = pillTabletModel;
            pillTabletCount++;
        } else if (spawnedCount < numNormalPills + numPillTablets + numVitaminPills) {
            // Vitamin pill (ve 3. a vyšších kolech)
            isVitaminPill = true;
            isPoison = vitaminPillCount === vitaminPoisonIndex;
            addsToxicity = !isPoison && roundNumber >= 3; // Nejedovaté vitamin pills přidávají 2 toxikace
            modelToUse = vitaminPillModel;
            vitaminPillCount++;
        } else {
            // Special pill (ve 4. a vyšších kolech)
            isSpecialPill = true;
            isPoison = specialPillPoisonIndices.includes(specialPillCount);
            adds2Toxicity = specialPillCount === specialPillAdds2ToxIndex;
            addsLife = specialPillCount === specialPillAddsLifeIndex;
            modelToUse = pillModel; // Použít základní pill model
            specialPillCount++;
        }
        
        if (!modelToUse) {
            spawnedCount++;
            return; // Model ještě není načten
        }
        
        const { group, boxSize } = normalizeAndCenterModel(modelToUse.clone(), 0.35);
        
        // Označit typ pilulky
        group.userData = { 
            isPoison: isPoison, 
            isVitaminPill: isVitaminPill,
            isPillTablet: isPillTablet,
            isSpecialPill: isSpecialPill,
            reducesToxicity: reducesToxicity,
            addsToxicity: addsToxicity,
            adds2Toxicity: adds2Toxicity,
            addsLife: addsLife,
            id: spawnedCount, 
            type: 'pill' 
        };
        
        // Uložit informace o pilulce do fixního seznamu kola
        currentRoundPills.push({
            isPoison: isPoison,
            isVitaminPill: isVitaminPill,
            isPillTablet: isPillTablet,
            isSpecialPill: isSpecialPill,
            reducesToxicity: reducesToxicity,
            addsToxicity: addsToxicity,
            adds2Toxicity: adds2Toxicity,
            addsLife: addsLife
        });
        
        // Změnit barvy modelů
        group.traverse(c => {
            if (c.isMesh && c.material) {
                c.material = c.material.clone();
                if (isSpecialPill) {
                    // Special pill - polovina zelená, polovina tmavě fialová
                    applySpecialPillColor(c);
                } else if (isVitaminPill) {
                    // Vitamin pills - zelená
                    c.material.color.set(0x00ff00);
                } else if (isPillTablet) {
                    // Pilltablet - světle modrá
                    c.material.color.set(0x87ceeb);
                }
            }
        });
        
        scene.add(group);

        // Pro pilltablet a vitamin pills použít Box shape pro lepší stabilitu, jinak Cylinder
        let shape;
        let spawnHeightOffset = 0; // Dodatečná výška pro spawn
        
        if (isPillTablet || isVitaminPill) {
            // Pilltablet a vitamin pills - Box shape pro stabilitu (ležící naplocho)
            const halfExtents = new CANNON.Vec3(
                Math.max(boxSize.x, boxSize.z) / 2 * 1.0,
                boxSize.y / 2 * 1.0,
                Math.min(boxSize.x, boxSize.z) / 2 * 1.0
            );
            shape = new CANNON.Box(halfExtents);
            spawnHeightOffset = 0.15; // Více nad stolem pro pilltablet a vitamin pills
        } else {
            // Normální pilulky - Cylinder
            const pR = Math.max(boxSize.x, boxSize.z) / 2 * 1.0; 
            const pH = boxSize.y * 1.0;
            shape = new CANNON.Cylinder(pR, pR, pH, 8);
        }
        
        // Spawn na pozici HRDLA lahve - VNĚ lahve!
        const bottlePos = bottleBodyRef.position;
        const bottleQuat = bottleBodyRef.quaternion;
        
        // Lokální pozice hrdla: (0, h/2, 0) - vrch lahve
        const localMouth = new CANNON.Vec3(0, h/2, 0);
        
        // Transform do world space - pozice hrdla
        const worldMouthPos = new CANNON.Vec3();
        bottleQuat.vmult(localMouth, worldMouthPos);
        worldMouthPos.vadd(bottlePos, worldMouthPos);
        
        // Směr hrdla (lokální Y=1 transformovaný do world space) - kam hrdlo míří
        const localUp = new CANNON.Vec3(0, 1, 0);
        const worldMouthDir = new CANNON.Vec3();
        bottleQuat.vmult(localUp, worldMouthDir);
        
        // Spawnujme VNĚ stěny - minimálně (r + tloušťka stěny + bezpečnost) od středu lahve
        const safeDistance = r * 1.2 + 0.2; // Bezpečně vně stěny
        const spawnOffset = new CANNON.Vec3(
            worldMouthDir.x * safeDistance,
            worldMouthDir.y * safeDistance + spawnHeightOffset, // Dodatečná výška pro pilltablet
            worldMouthDir.z * safeDistance
        );
        
        // Plus malý náhodný rozptyl
        const randomOffset = new CANNON.Vec3(
            (Math.random()-0.5) * 0.1,
            (Math.random()-0.5) * 0.1,
            (Math.random()-0.5) * 0.1
        );
        
        const spawnPos = new CANNON.Vec3(
            worldMouthPos.x + spawnOffset.x + randomOffset.x,
            worldMouthPos.y + spawnOffset.y + randomOffset.y,
            worldMouthPos.z + spawnOffset.z + randomOffset.z
        );
        
        const body = new CANNON.Body({
            mass: 0.05,
            position: spawnPos,
            material: world.defaultMaterial
        });
        
        body.ccdSpeedThreshold = 0.1;
        body.ccdIterations = 5;

        // Pro pilltablet a vitamin pills - ležící naplocho (bez rotace), pro ostatní - horizontální orientace
        if (isPillTablet || isVitaminPill) {
            // Pilltablet a vitamin pills - Box už je správně orientovaný (ležící naplocho)
            body.addShape(shape);
        } else {
            // Normální pilulky - horizontální orientace (ležící)
            const q = new CANNON.Quaternion();
            q.setFromAxisAngle(new CANNON.Vec3(1,0,0), Math.PI/2);
            body.addShape(shape, new CANNON.Vec3(0,0,0), q);
        }
        body.linearDamping = 0.5;
        
        // Počáteční rychlost - padají ve směru hrdla (kam míří)
        // Pokud je lahev otočená dnem vzhůru, hrdlo míří dolů, tak padají dolů
        // Omezit rychlost první pilulky, pokud je lahev držená (aby nevystřelila s víčkem)
        let baseSpeed = 1.0 + Math.random() * 0.5;
        if (spawnedCount === 0 && isDragging && draggingObject === 'bottle') {
            baseSpeed = 0.5 + Math.random() * 0.3; // Nižší rychlost pro první pilulku při držení
        }
        
        // Směr hrdla (kam míří) - to je směr, kam pilulky padají
        const worldMouthDirection = bottleBodyRef.quaternion.vmult(new CANNON.Vec3(0, 1, 0));
        
        // Malý náhodný rozptyl
        const randomSpread = new CANNON.Vec3(
            (Math.random()-0.5) * 0.3,
            (Math.random()-0.5) * 0.3,
            (Math.random()-0.5) * 0.3
        );
        
        body.velocity.set(
            worldMouthDirection.x * baseSpeed + randomSpread.x,
            worldMouthDirection.y * baseSpeed + randomSpread.y,
            worldMouthDirection.z * baseSpeed + randomSpread.z
        );
        
        world.addBody(body);
        objectsToUpdate.push({ mesh: group, body: body, isPill: true });
        
        spawnedCount++;
    };
    
    // Spawn první pilulku s malou prodlevou, aby se víčko stihlo odlepit, pak každých 0.2 sekundy
    setTimeout(() => {
        spawnPill();
        pillSpawnInterval = setInterval(spawnPill, 200);
    }, 100); // 100ms prodleva před prvním spawnem
}

function spawnPillsInside(radius, height) {
    if (!pillModel) return;
    for (let i = 0; i < 4; i++) {
        // Zvětšíme pilulky (0.25 -> 0.35)
        const { group, boxSize } = normalizeAndCenterModel(pillModel.clone(), 0.35);
        group.traverse(c => { if(c.isMesh) c.material = c.material.clone(); });
        scene.add(group);

        const pR = Math.max(boxSize.x, boxSize.z) / 2 * 1.0; 
        const pH = boxSize.y * 1.0;
        const shape = new CANNON.Cylinder(pR, pR, pH, 8);
        
        // safeRadius - pilulky spawnujeme blíže středu, aby se vešly
        const safeRadius = radius * 0.4; // Zvětšeno, ale stále bezpečné
        
        // Lahev je na Y=1.0
        // Spawnujeme pilulky ve střední části lahve
        const bottleCenterY = 1.0;
        const spawnY = bottleCenterY - height/4 + (i * height * 0.15); // Těsněji u sebe
        
        const body = new CANNON.Body({
            mass: 0.05,
            position: new CANNON.Vec3(
                (Math.random()-0.5)*safeRadius, 
                spawnY, 
                (Math.random()-0.5)*safeRadius
            ), 
            material: world.defaultMaterial
        });
        
        // Zapnout CCD pro pilulky
        body.ccdSpeedThreshold = 0.1;
        body.ccdIterations = 5;

        // HORIZONTÁLNÍ orientace (ležící) - lépe projdou hrdlem
        const q = new CANNON.Quaternion();
        q.setFromAxisAngle(new CANNON.Vec3(1,0,0), Math.PI/2);
        
        body.addShape(shape, new CANNON.Vec3(0,0,0), q);
        body.linearDamping = 0.5; 
        
        world.addBody(body);
        objectsToUpdate.push({ mesh: group, body: body, isPill: true });
    }
}

// --- TEXTURY MINCE ---
function createCoinTexture(isHappy) {
    const canvas = document.createElement('canvas');
    canvas.width = 256; canvas.height = 256;
    const ctx = canvas.getContext('2d');

    ctx.fillStyle = isHappy ? '#FFD700' : '#B22222'; 
    ctx.beginPath();
    ctx.arc(128, 128, 128, 0, Math.PI * 2);
    ctx.fill();

    ctx.strokeStyle = '#B8860B';
    ctx.lineWidth = 10;
    ctx.stroke();

    ctx.fillStyle = '#000';
    ctx.beginPath();
    if (isHappy) {
        ctx.arc(80, 90, 15, 0, Math.PI * 2);
        ctx.arc(176, 90, 15, 0, Math.PI * 2);
    } else {
        ctx.font = 'bold 60px Arial';
        ctx.fillText('X', 60, 110);
        ctx.fillText('X', 156, 110);
    }
    ctx.fill();

    ctx.strokeStyle = '#000';
    ctx.lineWidth = 10;
    ctx.beginPath();
    if (isHappy) {
        ctx.arc(128, 140, 70, 0, Math.PI, false); 
    } else {
        ctx.arc(128, 200, 70, Math.PI, 0, false); 
    }
    ctx.stroke();

    const tex = new THREE.CanvasTexture(canvas);
    return tex;
}

// Sdílené materiály pro minci
let coinMatSide, coinMatHappy, coinMatSad;
function initCoinMaterials() {
    if (coinMatSide) return;
    coinMatSide = new THREE.MeshLambertMaterial({ color: 0xD4AF37 }); // Jednodušší materiál pro výkon
    coinMatHappy = new THREE.MeshLambertMaterial({ map: createCoinTexture(true) });
    coinMatSad = new THREE.MeshLambertMaterial({ map: createCoinTexture(false) });
}

function createPreviewCoin() {
    initCoinMaterials();
    const geo = new THREE.CylinderGeometry(0.3, 0.3, 0.05, 32);
    previewCoinMesh = new THREE.Mesh(geo, [coinMatSide, coinMatHappy, coinMatSad]);
    
    // Umístíme doprostřed, kousek nad stůl (0.5m)
    previewCoinMesh.position.set(0, 0.5, 0);
    previewCoinMesh.rotation.x = Math.PI / 2; 
    
    previewCoinMesh.name = "PreviewCoin";
    scene.add(previewCoinMesh);
}

function createCoin(pos, quat) {
    initCoinMaterials();

    const geo = new THREE.CylinderGeometry(0.2, 0.2, 0.05, 32);
    coinMesh = new THREE.Mesh(geo, [coinMatSide, coinMatHappy, coinMatSad]);
    coinMesh.castShadow = false; // Vypnout stíny pro výkon
    coinMesh.receiveShadow = false; // Vypnout stíny pro výkon
    scene.add(coinMesh);

    // Fyzika - BOX (kvádr) pro maximální stabilitu
    // Vizuál je válec (0.2 radius), box bude mít strany 0.4x0.4
    const halfExtents = new CANNON.Vec3(0.2, 0.05, 0.2); // Y je tloušťka (polovina z 0.1)
    const shape = new CANNON.Box(halfExtents);
    
    coinBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(pos.x, pos.y + 0.2, pos.z), 
        material: world.defaultMaterial,
        linearDamping: 0.5, 
        angularDamping: 0.5
    });
    
    // Zapnout CCD
    coinBody.ccdSpeedThreshold = 0.5; 
    coinBody.ccdIterations = 2;
    
    // Box v Cannonu je axis-aligned. My ho chceme rotovat, aby ležel "naplocho" (Y osy boxu jsou malé)
    // Vizuál mince (Cylinder) jsme vytvořili s orientací Y-up (plochá strana nahoře).
    // Box 0.2x0.05x0.2 je taky "placka" ležící na zemi (Y je výška).
    // Takže nemusíme rotovat shape, jen samotné těleso se bude rotovat při letu.
    
    // Ale pozor: visual mince (CylinderGeometry) má osu Y jako osu válce.
    // Preview mince byla otočena o 90deg kolem X, aby byla vidět.
    // Zde v createCoin jsme dříve aplikovali rotaci tělesa nebo shape.
    
    // Aplikujeme startovní rotaci
    // Náhodný náklon, aby nedopadla vždy stejně
    // quat pro srovnání BOXu do Y (pokud je to potřeba, ale pro Box to není nutné, leží naplocho)
    // Ale chceme, aby při spawnu už byla trochu "našikmo"
    const randAxis = new CANNON.Vec3(Math.random(), Math.random(), Math.random()).unit();
    const randAngle = (Math.random() - 0.5) * Math.PI; // +/- 90 deg náhodně
    
    const q = new CANNON.Quaternion();
    q.setFromAxisAngle(randAxis, randAngle);
    
    coinBody.quaternion.copy(q);
    coinBody.addShape(shape);
    
    // Výskok a rotace - VÍCE NÁHODY
    // Rychlost nahoru 4-7, do stran +/- 2
    coinBody.velocity.set(
        (Math.random()-0.5) * 4, 
        4 + Math.random() * 3, 
        (Math.random()-0.5) * 4
    ); 
    // Rotace: velmi divoká
    coinBody.angularVelocity.set(
        (Math.random()-0.5) * 20, 
        (Math.random()-0.5) * 20, 
        (Math.random()-0.5) * 20
    ); 

    world.addBody(coinBody);
    objectsToUpdate.push({ mesh: coinMesh, body: coinBody, isCoin: true });
    
    // Timeout
    setTimeout(() => {
        if (coinBody && gameState === STATE.COIN_FLYING) {
            coinBody.velocity.set(0,0,0);
            coinBody.angularVelocity.set(0,0,0);
        }
    }, 5000);
}

function startCoinToss() {
    gameState = STATE.WAITING_FOR_TOSS;
    showStatus("", false); // Čisté UI
    createPreviewCoin();
}

function openBottle() {
    if (isBottleOpen) return;
    detachCap();
}

function onMouseDown(event) {
    if (gameState === STATE.COIN_FLYING) return;

    mouse.x = (event.clientX / window.innerWidth) * 2 - 1;
    mouse.y = -(event.clientY / window.innerHeight) * 2 + 1;
    raycaster.setFromCamera(mouse, camera);

    // 1. Interakce s mincí (jako dříve)
    if (gameState === STATE.WAITING_FOR_TOSS || gameState === STATE.COIN_LANDED) {
        handleCoinClick(event);
        return;
    }

    // 2. Interakce s objekty (lahve, víčka, pilulky)
    const intersects = raycaster.intersectObjects(scene.children, true);
    for(let hit of intersects) {
        let obj = hit.object;
        
        // Kontrola, zda klikl na BottleGroup, Víčko, Pilulku, Injector, Tester, Kleště, Zub, Candy nebo Brain
        let isBottle = false;
        let isCap = false;
        let pillGroup = null;
        let isInjector = false;
        let isTester = false;
        let isPliers = false;
        let isTooth = false;
        let isCandy = false;
        let isBrain = false;
        let isLeech = false;
        let isHammer = false;
        let isHearth = false;

        let tempObj = obj;
        while(tempObj) {
            if (tempObj.name === "BottleGroup") {
                isBottle = true;
                break;
            }
            if (tempObj === capMesh) {
                isCap = true;
                break;
            }
            if (tempObj.name === "InjectorGroup") {
                isInjector = true;
                break;
            }
            if (tempObj.name === "TesterGroup") {
                isTester = true;
                break;
            }
            if (tempObj.name === "PliersGroup") {
                isPliers = true;
                break;
            }
            if (tempObj.name === "ToothGroup") {
                isTooth = true;
                break;
            }
            if (tempObj.name === "CandyGroup") {
                isCandy = true;
                break;
            }
            if (tempObj.name === "BrainGroup") {
                isBrain = true;
                break;
            }
            if (tempObj.name === "LeechGroup") {
                isLeech = true;
                break;
            }
            if (tempObj.name === "HammerGroup") {
                isHammer = true;
                break;
            }
            if (tempObj.name === "HearthGroup") {
                isHearth = true;
                break;
            }
            if (tempObj.userData && tempObj.userData.type === 'pill') {
                pillGroup = tempObj;
                break;
            }
            tempObj = tempObj.parent;
        }

        // 3. PRÁŠKY - pouze hráč na tahu
        if (pillGroup && gameState === STATE.PLAYER_TURN) {
            // Uložit referenci na pilulku a počáteční pozici myši pro rozlišení kliknutí vs drag
            potentialPillGroup = pillGroup;
            mouseDownPos.x = event.clientX;
            mouseDownPos.y = event.clientY;
            hasMoved = false;
            
            // Najít těleso pilulky
            const item = objectsToUpdate.find(o => o.mesh === pillGroup || o.mesh === pillGroup.parent);
            if (item && item.body) {
                potentialPillBody = item.body;
            }
            return; // Nechat onMouseMove a onMouseUp rozhodnout, zda kliknutí nebo drag
        }

        // Drag víčko (pokud je odpadlé a existuje) - hráč může vždy
        if (isCap && capBody && isBottleOpen) {
            isDragging = true;
            draggingObject = 'cap';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, capBody);
            return;
        }

        // Drag bottle - hráč může vždy (aby mohl otevřít i když prohrál minci)
        if (isBottle && bottleBody) {
            isDragging = true;
            draggingObject = 'bottle';
            currentLift = 0; // Reset zvedání - začínáme tam, kde lahev je
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, bottleBody);
            return;
        }

        // Drag testovací itemy (ze spawn tlačítka) - vždy povolit
        if (isInjector && injectorBody) {
            isDragging = true;
            draggingObject = 'injector';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, injectorBody);
            return;
        }

        if (isTester && testerBody) {
            isDragging = true;
            draggingObject = 'tester';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, testerBody);
            return;
        }

        if (isPliers && pliersBody) {
            isDragging = true;
            draggingObject = 'pliers';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, pliersBody);
            return;
        }

        if (isTooth && toothBody) {
            isDragging = true;
            draggingObject = 'tooth';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, toothBody);
            return;
        }

        if (isCandy && candyBody) {
            isDragging = true;
            draggingObject = 'candy';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, candyBody);
            return;
        }

        if (isBrain && brainBody) {
            isDragging = true;
            draggingObject = 'brain';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, brainBody);
            return;
        }

        if (isLeech && leechBody) {
            isDragging = true;
            draggingObject = 'leech';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, leechBody);
            return;
        }

        if (isHammer && hammerBody) {
            isDragging = true;
            draggingObject = 'hammer';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, hammerBody);
            return;
        }

        if (isHearth && hearthBody) {
            isDragging = true;
            draggingObject = 'hearth';
            addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, hearthBody);
            return;
        }

        // Drag shop itemy - pouze pokud jsou vlastněné hráčem a hráč je na tahu
        if (gameState === STATE.PLAYER_TURN) {
            // Najít shop item v objectsToUpdate podle mesh
            let itemData = null;
            let itemBody = null;
            let itemType = null;
            
            // Projít všechny objekty a najít ten, který byl kliknut
            for (let item of objectsToUpdate) {
                if (item.isShopItem && item.mesh) {
                    // Zkontrolovat, zda kliknutý objekt je součástí tohoto itemu
                    let checkObj = obj;
                    while (checkObj) {
                        if (checkObj === item.mesh || (item.mesh.children && item.mesh.children.includes(checkObj))) {
                            itemData = item;
                            itemBody = item.body;
                            itemType = item.itemType;
                            break;
                        }
                        checkObj = checkObj.parent;
                    }
                    if (itemData) break;
                }
            }
            
            // Kontrola vlastníka - pouze hráč může používat své itemy
            if (itemData && itemData.owner === 'player' && itemBody) {
                // Nastavit globální proměnné pro tento typ itemu
                if (itemType === 'injector') {
                    injectorGroup = itemData.mesh;
                    injectorBody = itemBody;
                } else if (itemType === 'tester') {
                    testerGroup = itemData.mesh;
                    testerBody = itemBody;
                } else if (itemType === 'pliers') {
                    pliersGroup = itemData.mesh;
                    pliersBody = itemBody;
                } else if (itemType === 'tooth') {
                    toothGroup = itemData.mesh;
                    toothBody = itemBody;
                } else if (itemType === 'candy') {
                    candyGroup = itemData.mesh;
                    candyBody = itemBody;
                } else if (itemType === 'brain') {
                    brainGroup = itemData.mesh;
                    brainBody = itemBody;
                } else if (itemType === 'leech') {
                    leechGroup = itemData.mesh;
                    leechBody = itemBody;
                }
                
                isDragging = true;
                draggingObject = itemType;
                addMouseConstraint(hit.point.x, hit.point.y, hit.point.z, itemBody);
                return;
            }
        }
    }
}

function handleCoinClick(event) {
    // Logika pro minci vytažená z onMouseClick
    if (gameState === STATE.WAITING_FOR_TOSS && previewCoinMesh) {
        const intersects = raycaster.intersectObject(previewCoinMesh);
        if (intersects.length > 0) {
            gameState = STATE.COIN_FLYING;
            const pos = previewCoinMesh.position.clone();
            const quat = previewCoinMesh.quaternion.clone();
            scene.remove(previewCoinMesh);
            previewCoinMesh = null;
            createCoin(pos, quat);
        }
    } else if (gameState === STATE.COIN_LANDED && coinMesh) {
        const intersects = raycaster.intersectObject(coinMesh);
        if (intersects.length > 0) {
            world.removeBody(coinBody);
            scene.remove(coinMesh);
            const idx = objectsToUpdate.findIndex(o => o.isCoin);
            if (idx !== -1) objectsToUpdate.splice(idx, 1);
            coinBody = null;
            coinMesh = null;
            spawnBottle();
            const playerStarts = intersects[0].object.userData.playerStarts;
            // roundNumber zůstává 1 pro první kolo - změní se až po otevření stolu
            if (playerStarts) {
                gameState = STATE.PLAYER_TURN;
                startPlayerTurn();
            } else {
                gameState = STATE.ENEMY_TURN;
                startEnemyTurn();
            }
        }
    }
}

function addMouseConstraint(x, y, z, body) {
    const constrainedBody = new CANNON.Body({ mass: 0 });
    constrainedBody.addShape(new CANNON.Sphere(0.1));
    constrainedBody.position.set(x, y, z);
    mouseTargetPos.set(x, y, z); // Inicializace cíle
    constrainedBody.collisionFilterGroup = 0;
    constrainedBody.collisionFilterMask = 0;
    world.addBody(constrainedBody);

    const v1 = new CANNON.Vec3(x,y,z).vsub(body.position); 
    const antiRot = body.quaternion.inverse(); 
    const pivot = antiRot.vmult(v1); 

    mouseConstraint = new CANNON.PointToPointConstraint(body, pivot, constrainedBody, new CANNON.Vec3(0,0,0));
    world.addConstraint(mouseConstraint);
    mouseConstraint.mouseBody = constrainedBody;
}

function onMouseMove(event) {
    mouse.x = (event.clientX / window.innerWidth) * 2 - 1;
    mouse.y = -(event.clientY / window.innerHeight) * 2 + 1;

    // Rychlost myši pro "šťouchnutí"
    const movementX = event.movementX || 0;
    const movementY = event.movementY || 0;
    
    // Kontrola, zda se myš pohnula při držení potenciální pilulky
    if (potentialPillGroup && potentialPillBody && !isDragging) {
        const dx = event.clientX - mouseDownPos.x;
        const dy = event.clientY - mouseDownPos.y;
        const distance = Math.sqrt(dx * dx + dy * dy);
        
        if (distance > DRAG_THRESHOLD) {
            // Myš se pohnula dostatečně - začít drag
            hasMoved = true;
            isDragging = true;
            draggingObject = 'pill';
            document.body.style.cursor = 'grabbing'; // Změnit kurzor na grabbing
            
            // Najít pozici pilulky pro constraint
            const pillPos = potentialPillBody.position;
            addMouseConstraint(pillPos.x, pillPos.y, pillPos.z, potentialPillBody);
        }
    }

        if (isDragging && mouseConstraint) {
            // Při dragu zobrazit grabbing kurzor
            if (draggingObject === 'pill' || draggingObject === 'injector' || draggingObject === 'tester' || draggingObject === 'pliers' || draggingObject === 'tooth' || draggingObject === 'candy' || draggingObject === 'brain' || draggingObject === 'leech' || draggingObject === 'hammer') {
                document.body.style.cursor = 'grabbing';
            }
        // Drag logika: pohybujeme bodem v prostoru
        raycaster.setFromCamera(mouse, camera);
        
        // Vzdálenost od kamery k objektu
        const dist = mouseConstraint.bodyA.position.distanceTo(camera.position);
        const vec = new THREE.Vector3(mouse.x, mouse.y, 0.5);
        vec.unproject(camera);
        vec.sub(camera.position).normalize();
        
        const newPos = camera.position.clone().add(vec.multiplyScalar(dist));
        
        // 1. ZVEDNUTÍ LAHVE - Plynulé
        // Zde v mouse move jen aktualizujeme X a Z pozici podle myši.
        // Y pozici necháme "přirozenou" podle raycastu a zvednutí přičteme až v animate()
        
        // Limit výšky myši podle typu objektu
        if (draggingObject === 'bottle') {
            newPos.y = Math.min(newPos.y, 1.0); // Lahev - nízko nad stolem
            newPos.y = Math.max(newPos.y, 0.0);
        } else if (draggingObject === 'pill') {
            newPos.y = Math.min(newPos.y, 2.0); // Pilulky - mohou být výše
            newPos.y = Math.max(newPos.y, 0.0);
        } else if (draggingObject === 'injector' || draggingObject === 'tester' || draggingObject === 'pliers' || draggingObject === 'tooth' || draggingObject === 'candy' || draggingObject === 'brain' || draggingObject === 'leech' || draggingObject === 'hammer' || draggingObject === 'hearth') {
            newPos.y = Math.min(newPos.y, 2.0); // Injector, Tester, Kleště, Zub, Candy, Brain, Leech a Hammer - mohou být výše
            newPos.y = Math.max(newPos.y, 0.0);
        } else {
            newPos.y = Math.min(newPos.y, 1.0);
            newPos.y = Math.max(newPos.y, 0.0);
        }

        mouseTargetPos.set(newPos.x, newPos.y, newPos.z);
        
        // Reset rychlosti, aby se nehromadila energie
        mouseConstraint.mouseBody.velocity.set(0,0,0);
        mouseConstraint.mouseBody.angularVelocity.set(0,0,0);

    } else {
        // Kurzor a HOVER EFEKT - optimalizováno pro výkon
        const now = performance.now();
        if (now - lastHoverCheck < HOVER_CHECK_INTERVAL) {
            return; // Skip hover check pro lepší výkon
        }
        lastHoverCheck = now;
        
        document.body.style.cursor = 'default';
        raycaster.setFromCamera(mouse, camera);
        
        // OPTIMALIZACE: Raycast pouze na interaktivní objekty, ne celou scénu!
        const interactiveObjects = [];
        
        // Přidat pouze interaktivní objekty
        if (bottleGroup) interactiveObjects.push(bottleGroup);
        if (previewCoinMesh) interactiveObjects.push(previewCoinMesh);
        if (coinMesh) interactiveObjects.push(coinMesh);
        if (capMesh && isBottleOpen) interactiveObjects.push(capMesh);
        if (injectorGroup) interactiveObjects.push(injectorGroup);
        if (testerGroup) interactiveObjects.push(testerGroup);
        if (pliersGroup) interactiveObjects.push(pliersGroup);
        if (toothGroup) interactiveObjects.push(toothGroup);
        if (candyGroup) interactiveObjects.push(candyGroup);
        if (brainGroup) interactiveObjects.push(brainGroup);
        if (leechGroup) interactiveObjects.push(leechGroup);
        if (hammerGroup) interactiveObjects.push(hammerGroup);
        if (hearthGroup) interactiveObjects.push(hearthGroup);
        
        // Přidat všechny pilulky z objectsToUpdate
        objectsToUpdate.forEach(obj => {
            if (obj.isPill && obj.mesh) {
                interactiveObjects.push(obj.mesh);
            }
        });
        
        // Raycast pouze na interaktivní objekty
        if (interactiveObjects.length === 0) return;
        const intersects = raycaster.intersectObjects(interactiveObjects, true);
        
        let hoveredItemName = null;
        
        for(let hit of intersects) {
            let obj = hit.object;
            let pillBody = null;

            // Hledání pilulky pro hover
            let tempObj = obj;
            while(tempObj) {
                if (tempObj.userData && tempObj.userData.type === 'pill') {
                    // Našli jsme pilulku vizuálně, najdeme těleso
                    const item = objectsToUpdate.find(o => o.mesh === tempObj || o.mesh === tempObj.parent);
                    if (item && item.body) pillBody = item.body;
                    break;
                }
                if (tempObj.name === "BottleGroup") {
                    document.body.style.cursor = 'pointer';
                    break;
                }
                if (tempObj.name === "InjectorGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'INJECTOR: -2 toxicity next pill';
                    break;
                }
                if (tempObj.name === "TesterGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'TESTER: Click pill to test';
                    break;
                }
                if (tempObj.name === "PliersGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'PLIERS: Enemy +1 toxicity';
                    break;
                }
                if (tempObj.name === "ToothGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'TOOTH: Negates pliers effect';
                    break;
                }
                if (tempObj.name === "CandyGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'CANDY: Skip turn on use';
                    break;
                }
                if (tempObj.name === "BrainGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'BRAIN: Enemy eats next pill';
                    break;
                }
                if (tempObj.name === "LeechGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'LEECH: Reduces toxicity to minimum';
                    break;
                }
                if (tempObj.name === "HammerGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'HAMMER: Destroy a pill';
                    break;
                }
                if (tempObj.name === "HearthGroup") {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'HEARTH: +1 life';
                    break;
                }
                if (tempObj === previewCoinMesh || tempObj === coinMesh) {
                    document.body.style.cursor = 'pointer';
                    hoveredItemName = 'COIN';
                    break;
                }
                if (tempObj === capMesh && isBottleOpen) {
                    document.body.style.cursor = 'pointer';
                    break;
                }
                tempObj = tempObj.parent;
            }

            // Zobrazit kurzor pro pilulku (bez fyziky - to způsobovalo lag)
            if (pillBody && gameState === STATE.PLAYER_TURN) {
                document.body.style.cursor = 'grab';
                
                // Pokud je pilulka testovaná, zobrazit efekt
                const pillMesh = tempObj.userData && tempObj.userData.type === 'pill' ? tempObj : (tempObj.parent && tempObj.parent.userData && tempObj.parent.userData.type === 'pill' ? tempObj.parent : null);
                if (testedPill && pillMesh && (pillMesh === testedPill || pillMesh.parent === testedPill || testedPill === pillMesh)) {
                    const pillData = testedPill.userData || {};
                    let effectText = '';
                    if (pillData.isPoison) {
                        effectText = 'DEATH';
                    } else if (pillData.reducesToxicity) {
                        effectText = '-2 TOXICITY';
                    } else if (pillData.addsToxicity) {
                        effectText = '+2 TOXICITY';
                    } else if (pillData.adds2Toxicity) {
                        effectText = '+2 TOXICITY';
                    } else if (pillData.addsLife) {
                        effectText = '+1 LIFE';
                    } else {
                        effectText = '+1 TOXICITY';
                    }
                    hoveredItemName = 'PILL: ' + effectText;
                }
                break; // Stačí první pilulka
            }
            
            // Pokud už máme pointer kurzor, můžeme skončit
            if (document.body.style.cursor === 'pointer' || hoveredItemName) {
                break;
            }
        }
        
        // Zobrazit nebo skrýt tooltip
        const tooltip = document.getElementById('item-tooltip');
        if (tooltip) {
            if (hoveredItemName) {
                tooltip.textContent = hoveredItemName;
                tooltip.style.display = 'block';
                tooltip.style.left = (event.clientX + 15) + 'px';
                tooltip.style.top = (event.clientY + 15) + 'px';
            } else {
                tooltip.style.display = 'none';
            }
        }
    }
}

function onMouseUp(event) {
    // Zpracování pilulky - kliknutí vs drag
    if (potentialPillGroup && !hasMoved && gameState === STATE.PLAYER_TURN) {
        // Tester mód - testovat pilulku
        if (isTesterActive) {
            testedPill = potentialPillGroup;
            isTesterActive = false;
        }
        // Brain mód - oponent sní pilulku
        else if (isBrainActive) {
            eatPill(potentialPillGroup, false); // Oponent sní
            isBrainActive = false;
        }
        // Hammer mód - zničit pilulku
        else if (isHammerActive) {
            isHammerActive = false;
            
            // Najít pilulku v objectsToUpdate a odstranit ji
            const pillIndex = objectsToUpdate.findIndex(o => o.mesh === potentialPillGroup || o.mesh === potentialPillGroup.parent);
            if (pillIndex !== -1) {
                const pillItem = objectsToUpdate[pillIndex];
                // Odstranit z fyziky
                if (pillItem.body) {
                    world.removeBody(pillItem.body);
                }
                // Odstranit ze scény
                if (pillItem.mesh) {
                    scene.remove(pillItem.mesh);
                }
                // Odstranit z objectsToUpdate
                objectsToUpdate.splice(pillIndex, 1);
                
                // Odstranit z currentRoundPills pokud tam je
                const roundPillIndex = currentRoundPills.findIndex(p => p.mesh === potentialPillGroup || p.mesh === potentialPillGroup.parent);
                if (roundPillIndex !== -1) {
                    currentRoundPills.splice(roundPillIndex, 1);
                }
                
                // Aktualizovat UI
                updatePillStatsUI();
            }
            return; // Neskipne kolo
        }
        // Normální režim - sníst pilulku
        else {
            eatPill(potentialPillGroup, true);
        }
    }
    
    // Reset proměnných pro pilulky
    potentialPillGroup = null;
    potentialPillBody = null;
    hasMoved = false;
    
    // Ukončit drag
    isDragging = false;
    draggingObject = null;
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
}

function detachCap() {
    if (!bottleBody || !capMesh || isBottleOpen) return;
    isBottleOpen = true;

    // 1. Odstranit Shape z bottleBody
    if (bottleBody.userData && bottleBody.userData.capShapeIndex !== undefined) {
         // Cannon removeShape vyžaduje instanci shape. Najdeme ji.
         // Ale pozor, indexy se mohou měnit? Ne, pokud neměníme jiné shapy.
         // Bezpečnější: Projít shapes a najít ten správný? Ne, věříme indexu.
         // Ale raději:
         const idx = bottleBody.userData.capShapeIndex;
         if (idx < bottleBody.shapes.length) {
             bottleBody.removeShape(bottleBody.shapes[idx]);
         }
    }

    // 2. Odlepit vizuál a zachovat pozici
    scene.attach(capMesh);

    // 3. Vytvořit fyzické těleso pro letící víčko
    const geo = capMesh.geometry;
    const r = geo.parameters.radiusTop;
    const h = geo.parameters.height;
    const shape = new CANNON.Box(new CANNON.Vec3(r, h/2, r));
    
    capBody = new CANNON.Body({
        mass: 0.5,
        position: new CANNON.Vec3(capMesh.position.x, capMesh.position.y, capMesh.position.z),
        material: world.defaultMaterial
    });
    capBody.quaternion.copy(capMesh.quaternion);
    capBody.addShape(shape);
    
    world.addBody(capBody);
    objectsToUpdate.push({ mesh: capMesh, body: capBody });

    // 4. Odstřelit víčko - snížit sílu, pokud je lahev držená
    const forceMultiplier = (isDragging && draggingObject === 'bottle') ? 1.5 : 3.0; // Menší síla, pokud je lahev držená
    const force = new CANNON.Vec3(0, forceMultiplier, 0); 
    const worldForce = capBody.quaternion.vmult(force);
    capBody.applyImpulse(worldForce, capBody.position);
    
    // 5. Začít spawnovat pilulky postupně z hrdla - s malou prodlevou pro první pilulku
    if (bottleBody.userData && bottleBody.userData.bottleRadius && bottleBody.userData.bottleHeight) {
        spawnPillsFromBottle(bottleBody, bottleBody.userData.bottleRadius, bottleBody.userData.bottleHeight);
        
        // Pokud je ENEMY_TURN, počkat na spawn pilulek a pak spustit AI
        if (gameState === STATE.ENEMY_TURN) {
            // Počkat na spawn všech pilulek (4 pilulky * 200ms interval + 1s na dopad)
            setTimeout(() => {
                if (gameState === STATE.ENEMY_TURN && isBottleOpen) {
                    enemyChoosePill();
                }
            }, 2000);
        }
    }
}

function onKeyDown(event) {
    if ((event.code === 'KeyE' || event.key === 'e' || event.key === 'E')) {
        if (isDragging && !isBottleOpen) {
            detachCap();
        }
        
        // Použití itemu při držení
        if (isDragging && draggingObject && gameState === STATE.PLAYER_TURN) {
            const itemType = draggingObject;
            if (itemType === 'injector' || itemType === 'tester' || itemType === 'pliers' || 
                itemType === 'tooth' || itemType === 'candy' || itemType === 'brain' || itemType === 'leech' || itemType === 'hammer' || itemType === 'hearth') {
                useItem(itemType);
            }
        }
    }
}

function useItem(itemType) {
    switch(itemType) {
        case 'injector':
            useInjector();
            break;
        case 'tester':
            useTester();
            break;
        case 'pliers':
            usePliers();
            break;
        case 'tooth':
            useTooth();
            break;
        case 'candy':
            useCandy();
            break;
        case 'brain':
            useBrain();
            break;
        case 'leech':
            useLeech();
            break;
        case 'hammer':
            useHammer();
            break;
        case 'hearth':
            useHearth();
            break;
    }
}

function useInjector() {
    if (!injectorGroup || !injectorBody) return;
    
    // Neguje 2 toxifikace z příští snězené pilulky
    injectorToxicityReduction = 2;
    
    // Odstranit injector ze scény
    scene.remove(injectorGroup);
    world.removeBody(injectorBody);
    const idx = objectsToUpdate.findIndex(o => o.body === injectorBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    injectorGroup = null;
    injectorBody = null;
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
}

function useTester() {
    if (!testerGroup || !testerBody) return;
    
    // Najít tester v objectsToUpdate
    const itemData = objectsToUpdate.find(o => o.body === testerBody);
    
    // Pokud je to shop item, zkontrolovat vlastníka
    if (itemData && itemData.isShopItem) {
        const isPlayer = itemData.owner === 'player';
        if (gameState === STATE.PLAYER_TURN && !isPlayer) return;
        if (gameState === STATE.ENEMY_TURN && isPlayer) return;
        
        // Odstranit z playerItems
        const playerIdx = playerItems.findIndex(i => i.body === testerBody);
        if (playerIdx !== -1) playerItems.splice(playerIdx, 1);
    }
    
    // Aktivovat tester mód
    isTesterActive = true;
    
    // Odstranit tester ze scény
    scene.remove(testerGroup);
    world.removeBody(testerBody);
    const idx = objectsToUpdate.findIndex(o => o.body === testerBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    
    testerGroup = null;
    testerBody = null;
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
}

function usePliers() {
    if (!pliersGroup || !pliersBody) return;
    
    // Najít pliers v objectsToUpdate
    const itemData = objectsToUpdate.find(o => o.body === pliersBody);
    
    // Pokud je to shop item, zkontrolovat vlastníka
    if (itemData && itemData.isShopItem) {
        const isPlayer = itemData.owner === 'player';
        if (gameState === STATE.PLAYER_TURN && !isPlayer) return;
        if (gameState === STATE.ENEMY_TURN && isPlayer) return;
        
        // Odstranit z playerItems
        const playerIdx = playerItems.findIndex(i => i.body === pliersBody);
        if (playerIdx !== -1) playerItems.splice(playerIdx, 1);
    }
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
    
    // Animovat kleště k ústům oponenta
    const pliersMesh = pliersGroup;
    const pliersBodyRef = pliersBody;
    
    // Odstranit z objectsToUpdate
    const idx = objectsToUpdate.findIndex(o => o.body === pliersBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    
    animateItemToMouth(pliersMesh, pliersBodyRef, false, () => {
        // Po dokončení animace - přidat oponentovi 1 toxifikaci
        enemyToxicity = Math.min(enemyToxicity + 1, 5);
        pliersToxicityAdded += 1;
        updateUI();
        
        pliersGroup = null;
        pliersBody = null;
    });
}

function useTooth() {
    if (!toothGroup || !toothBody) return;
    
    // Najít tooth v objectsToUpdate
    const itemData = objectsToUpdate.find(o => o.body === toothBody);
    
    // Pokud je to shop item, zkontrolovat vlastníka
    if (itemData && itemData.isShopItem) {
        const isPlayer = itemData.owner === 'player';
        if (gameState === STATE.PLAYER_TURN && !isPlayer) return;
        if (gameState === STATE.ENEMY_TURN && isPlayer) return;
        
        // Odstranit z playerItems
        const playerIdx = playerItems.findIndex(i => i.body === toothBody);
        if (playerIdx !== -1) playerItems.splice(playerIdx, 1);
    }
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
    
    // Animovat zub k ústům hráče
    const toothMesh = toothGroup;
    const toothBodyRef = toothBody;
    
    // Odstranit z objectsToUpdate
    const idx = objectsToUpdate.findIndex(o => o.body === toothBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    
    animateItemToMouth(toothMesh, toothBodyRef, true, () => {
        // Po dokončení animace - neguje efekt kleští
        if (pliersToxicityAdded > 0) {
            enemyToxicity = Math.max(0, enemyToxicity - pliersToxicityAdded);
            pliersToxicityAdded = 0;
            updateUI();
        }
        
        toothGroup = null;
        toothBody = null;
    });
}

function useHammer() {
    if (!hammerGroup || !hammerBody) return;
    
    // Najít hammer v objectsToUpdate
    const itemData = objectsToUpdate.find(o => o.body === hammerBody);
    
    // Pokud je to shop item, zkontrolovat vlastníka
    if (itemData && itemData.isShopItem) {
        const isPlayer = itemData.owner === 'player';
        if (gameState === STATE.PLAYER_TURN && !isPlayer) return;
        if (gameState === STATE.ENEMY_TURN && isPlayer) return;
        
        // Odstranit z playerItems
        const playerIdx = playerItems.findIndex(i => i.body === hammerBody);
        if (playerIdx !== -1) playerItems.splice(playerIdx, 1);
    }
    
    // Aktivovat hammer mód - příští kliknutí na pilulku ji zničí
    isHammerActive = true;
    
    // Odstranit hammer ze scény
    scene.remove(hammerGroup);
    world.removeBody(hammerBody);
    const idx = objectsToUpdate.findIndex(o => o.body === hammerBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    
    hammerGroup = null;
    hammerBody = null;
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
}

function useHearth() {
    if (!hearthGroup || !hearthBody) return;
    
    // Najít hearth v objectsToUpdate
    const itemData = objectsToUpdate.find(o => o.body === hearthBody);
    
    // Pokud je to shop item, zkontrolovat vlastníka
    if (itemData && itemData.isShopItem) {
        const isPlayer = itemData.owner === 'player';
        if (gameState === STATE.PLAYER_TURN && !isPlayer) return;
        if (gameState === STATE.ENEMY_TURN && isPlayer) return;
        
        // Odstranit z playerItems
        const playerIdx = playerItems.findIndex(i => i.body === hearthBody);
        if (playerIdx !== -1) playerItems.splice(playerIdx, 1);
    }
    
    // Přidat 1 život tomu, kdo použil hearth
    if (gameState === STATE.PLAYER_TURN) {
        playerHP = Math.min(playerHP + 1, 5); // Max 5 životů
    } else if (gameState === STATE.ENEMY_TURN) {
        enemyHP = Math.min(enemyHP + 1, 5); // Max 5 životů
    }
    updateUI();
    
    // Odstranit hearth ze scény
    scene.remove(hearthGroup);
    world.removeBody(hearthBody);
    const idx = objectsToUpdate.findIndex(o => o.body === hearthBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    
    hearthGroup = null;
    hearthBody = null;
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
}

function useCandy() {
    if (!candyGroup || !candyBody) return;
    
    // Najít candy v objectsToUpdate
    const itemData = objectsToUpdate.find(o => o.body === candyBody);
    
    // Pokud je to shop item, zkontrolovat vlastníka
    if (itemData && itemData.isShopItem) {
        const isPlayer = itemData.owner === 'player';
        if (gameState === STATE.PLAYER_TURN && !isPlayer) return;
        if (gameState === STATE.ENEMY_TURN && isPlayer) return;
        
        // Odstranit z playerItems
        const playerIdx = playerItems.findIndex(i => i.body === candyBody);
        if (playerIdx !== -1) playerItems.splice(playerIdx, 1);
    }
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
    
    // Animovat candy k ústům hráče
    const candyMesh = candyGroup;
    const candyBodyRef = candyBody;
    
    // Odstranit z objectsToUpdate
    const idx = objectsToUpdate.findIndex(o => o.body === candyBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    
    animateItemToMouth(candyMesh, candyBodyRef, true, () => {
        // Po dokončení animace - přejít na oponenta
        candyGroup = null;
        candyBody = null;
        gameState = STATE.ENEMY_TURN;
        startEnemyTurn();
    });
}

function useBrain() {
    if (!brainGroup || !brainBody) return;
    
    // Najít brain v objectsToUpdate
    const itemData = objectsToUpdate.find(o => o.body === brainBody);
    
    // Pokud je to shop item, zkontrolovat vlastníka
    if (itemData && itemData.isShopItem) {
        const isPlayer = itemData.owner === 'player';
        if (gameState === STATE.PLAYER_TURN && !isPlayer) return;
        if (gameState === STATE.ENEMY_TURN && isPlayer) return;
        
        // Odstranit z playerItems
        const playerIdx = playerItems.findIndex(i => i.body === brainBody);
        if (playerIdx !== -1) playerItems.splice(playerIdx, 1);
    }
    
    // Aktivovat brain mód - příští kliknutí na pilulku ji sní oponent
    isBrainActive = true;
    
    // Odstranit brain ze scény
    scene.remove(brainGroup);
    world.removeBody(brainBody);
    const idx = objectsToUpdate.findIndex(o => o.body === brainBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    
    brainGroup = null;
    brainBody = null;
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
}

function useLeech() {
    if (!leechGroup || !leechBody) return;
    
    // Najít leech v objectsToUpdate
    const itemData = objectsToUpdate.find(o => o.body === leechBody);
    
    // Pokud je to shop item, zkontrolovat vlastníka
    if (itemData && itemData.isShopItem) {
        const isPlayer = itemData.owner === 'player';
        if (gameState === STATE.PLAYER_TURN && !isPlayer) return;
        if (gameState === STATE.ENEMY_TURN && isPlayer) return;
        
        // Odstranit z playerItems
        const playerIdx = playerItems.findIndex(i => i.body === leechBody);
        if (playerIdx !== -1) playerItems.splice(playerIdx, 1);
    }
    
    // Snížit toxikaci na minimum (0)
    if (gameState === STATE.PLAYER_TURN) {
        playerToxicity = 0;
    } else if (gameState === STATE.ENEMY_TURN) {
        enemyToxicity = 0;
    }
    updateUI();
    
    // Odstranit leech ze scény
    scene.remove(leechGroup);
    world.removeBody(leechBody);
    const idx = objectsToUpdate.findIndex(o => o.body === leechBody);
    if (idx !== -1) objectsToUpdate.splice(idx, 1);
    
    leechGroup = null;
    leechBody = null;
    
    // Ukončit drag
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        world.removeBody(mouseConstraint.mouseBody);
        mouseConstraint = null;
    }
    isDragging = false;
    draggingObject = null;
}

function startPlayerTurn() {
    gameState = STATE.PLAYER_TURN;
    // Hráč je na tahu - může hýbat lahví (myší) a otevřít ji (E)
}

function startEnemyTurn() {
    gameState = STATE.ENEMY_TURN;
    
    setTimeout(() => {
        // AI pouze vybírá pilulku - lahev otevírá jen hráč
        if (isBottleOpen) {
            enemyChoosePill();
        } else {
            // Pokud lahev není otevřená, AI nemůže hrát - hráč musí otevřít
            // To by nemělo nastat, ale pro jistotu počkáme
            setTimeout(() => {
                if (isBottleOpen) {
                    enemyChoosePill();
                }
            }, 1000);
        }
    }, 1500);
}

function enemyChoosePill() {
    const availablePills = objectsToUpdate.filter(o => o.isPill);
    if (availablePills.length === 0) {
        // Došly pilulky? Reset kola nebo spawn nové lahve?
        // Prozatím nic, AI čeká.
        return;
    }
    const choice = availablePills[Math.floor(Math.random() * availablePills.length)];
    eatPill(choice.mesh, false);
}

function showGoodPillEffect() {
    const overlay = document.getElementById('effect-overlay');
    overlay.className = 'good-pill';
    overlay.style.opacity = '0';
    
    // Spustit animaci (LSD trip)
    overlay.classList.add('animate-good');
    
    // Po animaci odstranit třídu (animace trvá 1.5s)
    setTimeout(() => {
        overlay.classList.remove('animate-good');
        overlay.className = '';
        overlay.style.opacity = '0';
        overlay.style.filter = '';
        overlay.style.transform = '';
    }, 1500);
}

function showBadPillEffect() {
    const overlay = document.getElementById('effect-overlay');
    overlay.className = 'bad-pill';
    overlay.style.opacity = '0';
    
    // Spustit animaci (fade to black, pak fade in)
    overlay.classList.add('animate-bad');
    
    // Po animaci odstranit třídu
    setTimeout(() => {
        overlay.classList.remove('animate-bad');
        overlay.className = '';
        overlay.style.opacity = '0';
    }, 2500);
}

// Pomocná funkce pro výpočet pozice úst
function getMouthPosition(isPlayer) {
    // Pozice "úst" - kamera jsou oči, ústa jsou pod nimi, blízko kamery
    const cameraDirection = new THREE.Vector3();
    camera.getWorldDirection(cameraDirection);
    
    // Ústa jsou velmi blízko kamery (0.6 jednotek), výš (kamera Y=9, ústa Y≈8.5) a trochu dopředu
    // Kamera kouká dolů, takže ústa jsou před kamerou a trochu níž
    const mouthOffset = new THREE.Vector3(
        cameraDirection.x * 0.6,  // 0.6 jednotek před kamerou (velmi blízko)
        -0.5,  // 0.5 jednotky dolů od kamery (ústa pod očima)
        cameraDirection.z * 0.6
    );
    const mouthPosition = camera.position.clone().add(mouthOffset);
    
    // Pro AI použijeme pozici před zombie pusu
    if (isPlayer) {
        return mouthPosition;
    } else {
        // Pozice úst zombie - před jeho hlavou
        // Zombie je na zombieDebugPos, rotace je zombieDebugRot, scale je zombieDebugScale
        // Vypočítáme pozici hlavy a pak úst před ní
        
        // Výška úst od základny zombie (relativní k měřítku)
        // Zombie je na Y = -1.400, ústa by měla být přibližně ve výšce hlavy
        const mouthHeight = enemyMouthHeight * zombieDebugScale; // Výška úst od základny (použijeme debug hodnotu)
        
        // Směr před zombie podle rotace Y (horizontální směr, kam zombie kouká)
        const forwardDistance = 0.5 * zombieDebugScale; // Vzdálenost před zombie (před pusu)
        const forwardX = Math.sin(zombieDebugRot.y) * forwardDistance;
        const forwardZ = Math.cos(zombieDebugRot.y) * forwardDistance;
        
        // Pozice úst: pozice zombie + offset nahoru (hlava/ústa) + offset dopředu (před pusu)
        return new THREE.Vector3(
            zombieDebugPos.x + forwardX,
            zombieDebugPos.y + mouthHeight, // Ústa ve výšce hlavy
            zombieDebugPos.z + forwardZ // Dopředu před pusu
        );
    }
}

// Funkce pro animaci itemu k ústům (bez efektů pilulky)
function animateItemToMouth(itemMesh, itemBody, isPlayer, onComplete) {
    const targetMouthPos = getMouthPosition(isPlayer);
    const startPos = itemMesh.position.clone();
    const startRot = itemMesh.rotation.clone();
    const targetPos = targetMouthPos;
    const duration = 1200; // Fixní 1.2 sekundy pro plynulost
    const startTime = performance.now();
    
    // Odpojit fyziku - item letí ručně (STATICKÁ, bez rotace)
    if (itemBody) {
        itemBody.type = CANNON.Body.KINEMATIC;
        itemBody.velocity.set(0,0,0);
        itemBody.angularVelocity.set(0,0,0);
    }
    
    // Zastavit rotaci itemu - bude statická
    if (itemMesh) {
        itemMesh.rotation.copy(startRot);
    }
    
    function animate() {
        const elapsed = performance.now() - startTime;
        const progress = Math.min(elapsed / duration, 1);
        
        // Plynulý easing (ease-in-out cubic)
        const eased = progress < 0.5 
            ? 4 * progress * progress * progress
            : 1 - Math.pow(-2 * progress + 2, 3) / 2;
        
        // Interpolace pozice
        const currentPos = startPos.clone().lerp(targetPos, eased);
        
        // Zmenšování itemu (efekt polykání)
        const scale = 1 - eased * 0.7; // Zmenší se na 30% původní velikosti
        
        if (itemMesh) {
            itemMesh.position.copy(currentPos);
            itemMesh.scale.set(scale, scale, scale);
        }
        
        if (itemBody) {
            itemBody.position.set(currentPos.x, currentPos.y, currentPos.z);
            if (itemBody.quaternion) {
                itemBody.quaternion.set(0, 0, 0, 1); // Bez rotace
            }
        }
        
        if (progress < 1) {
            requestAnimationFrame(animate);
        } else {
            // Dosáhli jsme úst - odstranit item
            if (itemBody) {
                world.removeBody(itemBody);
            }
            if (itemMesh) {
                scene.remove(itemMesh);
            }
            
            // Zavolat callback po dokončení
            if (onComplete) {
                onComplete();
            }
        }
    }
    
    animate();
}

function animatePillToMouth(pillMesh, pillBody, isPlayer, isPoison, isVitaminPill = false, reducesToxicity = false, addsToxicity = false, adds2Toxicity = false, addsLife = false) {
    // Pozice "úst" - kamera jsou oči, ústa jsou pod nimi, blízko kamery
    const cameraDirection = new THREE.Vector3();
    camera.getWorldDirection(cameraDirection);
    
    // Ústa jsou velmi blízko kamery (0.6 jednotek), výš (kamera Y=9, ústa Y≈8.5) a trochu dopředu
    // Kamera kouká dolů, takže ústa jsou před kamerou a trochu níž
    const mouthOffset = new THREE.Vector3(
        cameraDirection.x * 0.6,  // 0.6 jednotek před kamerou (velmi blízko)
        -0.5,  // 0.5 jednotky dolů od kamery (ústa pod očima)
        cameraDirection.z * 0.6
    );
    const mouthPosition = camera.position.clone().add(mouthOffset);
    
    // Pro AI použijeme pozici před zombie pusu
    let targetMouthPos;
    if (isPlayer) {
        targetMouthPos = mouthPosition;
    } else {
        // Pozice úst zombie - před jeho hlavou
        // Zombie je na zombieDebugPos, rotace je zombieDebugRot, scale je zombieDebugScale
        // Vypočítáme pozici hlavy a pak úst před ní
        
        // Výška úst od základny zombie (relativní k měřítku)
        // Zombie je na Y = -1.400, ústa by měla být přibližně ve výšce hlavy
        const mouthHeight = enemyMouthHeight * zombieDebugScale; // Výška úst od základny (použijeme debug hodnotu)
        
        // Směr před zombie podle rotace Y (horizontální směr, kam zombie kouká)
        const forwardDistance = 0.5 * zombieDebugScale; // Vzdálenost před zombie (před pusu)
        const forwardX = Math.sin(zombieDebugRot.y) * forwardDistance;
        const forwardZ = Math.cos(zombieDebugRot.y) * forwardDistance;
        
        // Pozice úst: pozice zombie + offset nahoru (hlava/ústa) + offset dopředu (před pusu)
        targetMouthPos = new THREE.Vector3(
            zombieDebugPos.x + forwardX,
            zombieDebugPos.y + mouthHeight, // Ústa ve výšce hlavy
            zombieDebugPos.z + forwardZ // Dopředu před pusu
        );
    }
    
    const startPos = pillMesh.position.clone();
    const startRot = pillMesh.rotation.clone(); // Uložit původní rotaci
    const targetPos = targetMouthPos;
    const distance = startPos.distanceTo(targetPos);
    const duration = 1200; // Fixní 1.2 sekundy pro plynulost
    const startTime = performance.now();
    
    // Odpojit fyziku - pilulka letí ručně (STATICKÁ, bez rotace)
    if (pillBody) {
        pillBody.type = CANNON.Body.KINEMATIC;
        pillBody.velocity.set(0,0,0);
        pillBody.angularVelocity.set(0,0,0);
    }
    
    // Zastavit rotaci pilulky - bude statická
    if (pillMesh) {
        pillMesh.rotation.copy(startRot); // Nastavit na původní rotaci a nechat statickou
    }
    
    function animate() {
        const elapsed = performance.now() - startTime;
        const progress = Math.min(elapsed / duration, 1);
        
        // Plynulý easing (ease-in-out cubic)
        const eased = progress < 0.5 
            ? 4 * progress * progress * progress
            : 1 - Math.pow(-2 * progress + 2, 3) / 2;
        
        // Interpolace pozice
        const currentPos = startPos.clone().lerp(targetPos, eased);
        
        // Zmenšování pilulky (efekt polykání)
        const scale = 1 - eased * 0.7; // Zmenší se na 30% původní velikosti
        
        if (pillMesh) {
            pillMesh.position.copy(currentPos);
            pillMesh.scale.set(scale, scale, scale);
            // ŽÁDNÁ ROTACE - pilulka zůstává statická
            // pillMesh.rotation zůstává na startRot (nastaveno výše)
        }
        
        if (pillBody) {
            pillBody.position.set(currentPos.x, currentPos.y, currentPos.z);
            // Těleso také bez rotace
            if (pillBody.quaternion) {
                pillBody.quaternion.set(0, 0, 0, 1); // Bez rotace
            }
        }
        
        if (progress < 1) {
            requestAnimationFrame(animate);
        } else {
            // Dosáhli jsme úst - odstranit pilulku a spustit efekt
            if (pillBody) {
                world.removeBody(pillBody);
            }
            if (pillMesh) {
                scene.remove(pillMesh);
            }
            
            // Dramatická napínavá chvilka - hráč čeká, jestli byla pilulka v pořádku
            const suspenseDelay = isPlayer ? 2000 : 500; // 2 sekundy napětí pro hráče, 0.5s pro AI
            
            if (isPlayer) {
                if (isPoison) {
                    // Jedovatá pilulka (normální nebo vitamin) - ubrat život
                    setTimeout(() => {
                        showBadPillEffect();
                        playerHP--;
                        playerToxicity = 0; // Reset toxikace při ztrátě života
                        updateUI();
                        checkGameOver();
                        if (gameState !== STATE.GAME_OVER) {
                            // Zkontrolovat, zda jsou všechny pilulky snězeny
                            if (checkAllPillsEaten()) {
                                setTimeout(() => openTable(), 2500);
                            } else {
                                setTimeout(startEnemyTurn, 2500);
                            }
                        }
                    }, suspenseDelay);
                } else if (reducesToxicity) {
                    // Pilltablet, který redukuje toxikaci o 2
                    // Injector neovlivňuje redukci toxifikace
                    setTimeout(() => {
                        showGoodPillEffect();
                        // Redukovat toxikaci o 2 (min 0)
                        playerToxicity = Math.max(0, playerToxicity - 2);
                        updateUI();
                        
                        if (checkAllPillsEaten()) {
                            setTimeout(() => openTable(), 1500);
                        } else {
                            setTimeout(startEnemyTurn, 1500);
                        }
                    }, suspenseDelay);
                } else if (addsToxicity) {
                    // Vitamin pill (ve 3. kole), který přidává 2 toxikace
                    setTimeout(() => {
                        showGoodPillEffect();
                        // Aplikovat injector redukci
                        let toxicityToAdd = 2;
                        if (injectorToxicityReduction > 0) {
                            toxicityToAdd = Math.max(0, toxicityToAdd - injectorToxicityReduction);
                            injectorToxicityReduction = 0; // Reset po použití
                        }
                        playerToxicity += toxicityToAdd;
                        updateUI();
                        
                        // Pokud toxikace dosáhne 5 nebo více, vynulovat a ubrat život
                        if (playerToxicity >= 5) {
                            playerHP--;
                            playerToxicity = 0; // Reset toxikace při ztrátě života
                            updateUI();
                            checkGameOver();
                            
                            // Pokud hra neskončila, pokračovat
                            if (gameState !== STATE.GAME_OVER) {
                                if (checkAllPillsEaten()) {
                                    setTimeout(() => openTable(), 1500);
                                } else {
                                    setTimeout(startEnemyTurn, 1500);
                                }
                            }
                        } else {
                            // Toxikace ještě není 5, pokračovat normálně
                            if (checkAllPillsEaten()) {
                                setTimeout(() => openTable(), 1500);
                            } else {
                                setTimeout(startEnemyTurn, 1500);
                            }
                        }
                    }, suspenseDelay);
                } else if (adds2Toxicity) {
                    // Special pill, který přidává 2 toxicity
                    setTimeout(() => {
                        showGoodPillEffect();
                        // Aplikovat injector redukci
                        let toxicityToAdd = 2;
                        if (injectorToxicityReduction > 0) {
                            toxicityToAdd = Math.max(0, toxicityToAdd - injectorToxicityReduction);
                            injectorToxicityReduction = 0; // Reset po použití
                        }
                        playerToxicity += toxicityToAdd;
                        updateUI();
                        
                        // Pokud toxikace dosáhne 5 nebo více, vynulovat a ubrat život
                        if (playerToxicity >= 5) {
                            playerHP--;
                            playerToxicity = 0; // Reset toxikace při ztrátě života
                            updateUI();
                            checkGameOver();
                            
                            // Pokud hra neskončila, pokračovat
                            if (gameState !== STATE.GAME_OVER) {
                                if (checkAllPillsEaten()) {
                                    setTimeout(() => openTable(), 1500);
                                } else {
                                    setTimeout(startEnemyTurn, 1500);
                                }
                            }
                        } else {
                            // Toxikace ještě není 5, pokračovat normálně
                            if (checkAllPillsEaten()) {
                                setTimeout(() => openTable(), 1500);
                            } else {
                                setTimeout(startEnemyTurn, 1500);
                            }
                        }
                    }, suspenseDelay);
                } else if (addsLife) {
                    // Special pill, který přidává 1 život
                    setTimeout(() => {
                        showGoodPillEffect();
                        playerHP = Math.min(5, playerHP + 1); // Maximálně 5 životů
                        updateUI();
                        
                        if (checkAllPillsEaten()) {
                            setTimeout(() => openTable(), 1500);
                        } else {
                            setTimeout(startEnemyTurn, 1500);
                        }
                    }, suspenseDelay);
                } else {
                    // Normální dobrá pilulka přidá toxikaci
                    setTimeout(() => {
                        // Dobrá pilulka přidá toxikaci
                        // Aplikovat injector redukci
                        let toxicityToAdd = 1;
                        if (injectorToxicityReduction > 0) {
                            toxicityToAdd = Math.max(0, toxicityToAdd - injectorToxicityReduction);
                            injectorToxicityReduction = 0; // Reset po použití
                        }
                        playerToxicity += toxicityToAdd;
                        showGoodPillEffect();
                        updateUI();
                        
                        // Pokud toxikace dosáhne 5, vynulovat a ubrat život
                        if (playerToxicity >= 5) {
                            playerHP--;
                            playerToxicity = 0; // Reset toxikace při ztrátě života
                            updateUI();
                            checkGameOver();
                            
                            // Pokud hra neskončila, pokračovat
                            if (gameState !== STATE.GAME_OVER) {
                                if (checkAllPillsEaten()) {
                                    setTimeout(() => openTable(), 1500);
                                } else {
                                    setTimeout(startEnemyTurn, 1500);
                                }
                            }
                        } else {
                            // Toxikace ještě není 5, pokračovat normálně
                            if (checkAllPillsEaten()) {
                                setTimeout(() => openTable(), 1500);
                            } else {
                                setTimeout(startEnemyTurn, 1500);
                            }
                        }
                    }, suspenseDelay);
                }
            } else {
                // AI efekty (jen logika, žádné vizuální efekty)
                setTimeout(() => {
                    if (isPoison) {
                        // Jedovatá pilulka (normální nebo vitamin) - ubrat život
                        enemyHP--;
                        updateUI();
                        checkGameOver();
                        if (gameState !== STATE.GAME_OVER) {
                            if (checkAllPillsEaten()) {
                                setTimeout(() => openTable(), 2000);
                            } else {
                                setTimeout(startPlayerTurn, 2000);
                            }
                        }
                    } else if (reducesToxicity) {
                        // Pilltablet, který redukuje toxikaci o 2
                        enemyToxicity = Math.max(0, enemyToxicity - 2);
                        updateUI();
                        
                        if (checkAllPillsEaten()) {
                            setTimeout(() => openTable(), 1500);
                        } else {
                            setTimeout(startPlayerTurn, 1500);
                        }
                    } else if (addsToxicity) {
                        // Vitamin pill (ve 3. kole), který přidává 2 toxikace
                        enemyToxicity += 2;
                        updateUI();
                        
                        // Pokud toxikace dosáhne 5 nebo více, vynulovat a ubrat život
                        if (enemyToxicity >= 5) {
                            enemyToxicity = 0;
                            enemyHP--;
                            updateUI();
                            checkGameOver();
                        }
                        
                        if (checkAllPillsEaten()) {
                            setTimeout(() => openTable(), 1500);
                        } else {
                            setTimeout(startPlayerTurn, 1500);
                        }
                    } else if (adds2Toxicity) {
                        // Special pill, který přidává 2 toxicity
                        enemyToxicity += 2;
                        updateUI();
                        
                        // Pokud toxikace dosáhne 5 nebo více, vynulovat a ubrat život
                        if (enemyToxicity >= 5) {
                            enemyToxicity = 0;
                            enemyHP--;
                            updateUI();
                            checkGameOver();
                        }
                        
                        if (checkAllPillsEaten()) {
                            setTimeout(() => openTable(), 1500);
                        } else {
                            setTimeout(startPlayerTurn, 1500);
                        }
                    } else if (addsLife) {
                        // Special pill, který přidává 1 život
                        enemyHP = Math.min(5, enemyHP + 1); // Maximálně 5 životů
                        updateUI();
                        
                        if (checkAllPillsEaten()) {
                            setTimeout(() => openTable(), 1500);
                        } else {
                            setTimeout(startPlayerTurn, 1500);
                        }
                    } else {
                        // Normální dobrá pilulka přidá toxikaci oponentovi
                        enemyToxicity++;
                        updateUI();
                        
                        // Pokud toxikace dosáhne 5, vynulovat a ubrat život
                        if (enemyToxicity >= 5) {
                            enemyToxicity = 0;
                            enemyHP--;
                            updateUI();
                            checkGameOver();
                        }
                        
                        // Zkontrolovat, zda jsou všechny pilulky snězeny
                        if (gameState !== STATE.GAME_OVER) {
                            if (checkAllPillsEaten()) {
                                setTimeout(() => openTable(), 1500);
                            } else {
                                if (enemyToxicity >= 5) {
                                    setTimeout(startPlayerTurn, 2000);
                                } else {
                                    setTimeout(startPlayerTurn, 1500);
                                }
                            }
                        }
                    }
                }, suspenseDelay);
            }
        }
    }
    
    animate();
}

function eatPill(meshGroup, isPlayer) {
    const index = objectsToUpdate.findIndex(o => o.mesh === meshGroup);
    if (index === -1) return;
    
    const item = objectsToUpdate[index];
    const isPoison = meshGroup.userData.isPoison;
    const isVitaminPill = meshGroup.userData.isVitaminPill || false;
    const reducesToxicity = meshGroup.userData.reducesToxicity || false;
    const addsToxicity = meshGroup.userData.addsToxicity || false;
    const adds2Toxicity = meshGroup.userData.adds2Toxicity || false;
    const addsLife = meshGroup.userData.addsLife || false;
    
    // Odstranit z objectsToUpdate, aby se už neupdatovala přes fyziku
    objectsToUpdate.splice(index, 1);
    // Statistiky se už neaktualizují - zobrazují se všechny pilulky z kola (fixní seznam)
    
    // Spustit animaci k ústům
    animatePillToMouth(item.mesh, item.body, isPlayer, isPoison, isVitaminPill, reducesToxicity, addsToxicity, adds2Toxicity, addsLife);
}

function checkAllPillsEaten() {
    const remainingPills = objectsToUpdate.filter(o => o.isPill);
    return remainingPills.length === 0;
}

function openTable() {
    // NOVÝ PŘÍSTUP: Čisté THREE.js animace bez fyziky
    const openDuration = 2000; // 2 sekundy pro otevření stolu
    const slideDuration = 1500; // 1.5 sekundy pro sklouznutí objektů
    const startTime = performance.now();
    
    // Uložit původní rotace
    const leftStartRot = tableLeftMesh.rotation.x;
    const rightStartRot = tableRightMesh.rotation.x;
    const targetRot = Math.PI / 2; // 90 stupňů
    
    // Získat všechny objekty na stole a převést je na kinematic (odstranit z fyziky)
    const objectsToSlide = [];
    
    if (bottleBody && bottleGroup && bottleGroup.parent) {
        // Odstranit z fyziky a uložit pro animaci
        bottleBody.type = CANNON.Body.KINEMATIC;
        bottleBody.velocity.set(0, 0, 0);
        bottleBody.angularVelocity.set(0, 0, 0);
        const startPos = bottleGroup.position.clone();
        objectsToSlide.push({ 
            mesh: bottleGroup, 
            body: bottleBody,
            startPos: startPos,
            isBottle: true
        });
    }
    
    if (capBody && capMesh && capMesh.parent) {
        capBody.type = CANNON.Body.KINEMATIC;
        capBody.velocity.set(0, 0, 0);
        capBody.angularVelocity.set(0, 0, 0);
        const startPos = capMesh.position.clone();
        objectsToSlide.push({ 
            mesh: capMesh, 
            body: capBody,
            startPos: startPos,
            isCap: true
        });
    }
    
    // Přidat všechny pilulky
    objectsToUpdate.forEach(item => {
        if (item.isPill && item.body && item.mesh && item.mesh.parent) {
            item.body.type = CANNON.Body.KINEMATIC;
            item.body.velocity.set(0, 0, 0);
            item.body.angularVelocity.set(0, 0, 0);
            const startPos = item.mesh.position.clone();
            objectsToSlide.push({ 
                mesh: item.mesh, 
                body: item.body,
                startPos: startPos,
                isPill: true
            });
        }
    });
    
    // Přidat itemy - ty se budou pohybovat se stolem (přilepené)
    objectsToUpdate.forEach(item => {
        if (item.isShopItem && item.body && item.mesh && item.mesh.parent) {
            item.body.type = CANNON.Body.KINEMATIC;
            item.body.velocity.set(0, 0, 0);
            item.body.angularVelocity.set(0, 0, 0);
            // Uložit relativní pozici k příslušné polovině stolu
            const isOnLeft = item.owner === 'enemy';
            const tableHalf = isOnLeft ? tableLeftMesh : tableRightMesh;
            const worldPos = item.mesh.position.clone();
            const localPos = new THREE.Vector3();
            tableHalf.worldToLocal(localPos.copy(worldPos));
            item.tableLocalPos = localPos;
            item.tableHalf = tableHalf;
        }
    });
    
    // Najít minimální a maximální Y pozici pro výpočet rychlosti
    let minY = Infinity;
    let maxY = -Infinity;
    objectsToSlide.forEach(obj => {
        const y = obj.startPos.y;
        if (y < minY) minY = y;
        if (y > maxY) maxY = y;
    });
    const yRange = Math.max(maxY - minY, 0.1); // Alespoň 0.1, aby se nedělilo nulou
    
    // Vypočítat rychlostní modifikátor pro každý objekt podle jeho výšky
    objectsToSlide.forEach(obj => {
        // Normalizovat Y pozici (0 = nejníž, 1 = nejvýš)
        const normalizedY = (obj.startPos.y - minY) / yRange;
        // Vyšší objekty budou mít pomalejší akceleraci na začátku (0.7-1.0 násobek rychlosti)
        obj.speedMultiplier = 0.7 + normalizedY * 0.3; // Vyšší = pomalejší start
    });
    
    // Odstranit stůl z fyziky - nebude bránit sklouznutí
    if (tableLeftBody) {
        world.removeBody(tableLeftBody);
        tableLeftBody = null;
    }
    if (tableRightBody) {
        world.removeBody(tableRightBody);
        tableRightBody = null;
    }
    
    // Odstranit mouse constraint pokud existuje
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        if (mouseConstraint.mouseBody) {
            world.removeBody(mouseConstraint.mouseBody);
        }
        mouseConstraint = null;
        isDragging = false;
        draggingObject = null;
    }
    
    function animateTable() {
        const elapsed = performance.now() - startTime;
        const tableProgress = Math.min(elapsed / openDuration, 1);
        const slideProgress = Math.min(Math.max((elapsed - 300) / slideDuration, 0), 1); // Začít o 300ms později
        
        // Easing pro stůl
        const tableEased = tableProgress < 0.5 
            ? 2 * tableProgress * tableProgress 
            : 1 - Math.pow(-2 * tableProgress + 2, 2) / 2;
        
        // Animace stolu - otevření
        const currentRot = leftStartRot + tableEased * targetRot;
        tableLeftMesh.rotation.x = currentRot;
        tableRightMesh.rotation.x = rightStartRot + tableEased * targetRot;
        
        // Trackery se automaticky pohybují se stolem, protože jsou jeho potomky
        
        // Animace itemů - pohyb se stolem (přilepené)
        objectsToUpdate.forEach(item => {
            if (item.isShopItem && item.tableLocalPos && item.tableHalf) {
                const worldPos = new THREE.Vector3();
                item.tableHalf.localToWorld(worldPos.copy(item.tableLocalPos));
                if (item.mesh) {
                    item.mesh.position.copy(worldPos);
                }
                if (item.body) {
                    item.body.position.set(worldPos.x, worldPos.y, worldPos.z);
                }
            }
        });
        
        // Animace objektů - sklouznutí dolů s individuální rychlostí
        let allAnimationsDone = true;
        
        objectsToSlide.forEach(obj => {
            if (obj.mesh && obj.body) {
                const mesh = obj.mesh;
                const startPos = obj.startPos;
                
                // Všechny objekty začínají padat okamžitě (bez delay)
                const objElapsed = Math.max(0, elapsed - 200); // Začít 200ms po startu (když se stůl začne otevírat)
                const objSlideDuration = slideDuration + 200; // Délka animace
                const objProgress = Math.min(objElapsed / objSlideDuration, 1);
                
                if (objProgress < 1) {
                    allAnimationsDone = false;
                }
                
                // Fyzikálně správná akcelerace - kvadratická funkce (začíná pomalu, zrychluje)
                // Použijeme t² pro začátek (akcelerace), pak přejdeme na rychlejší fázi
                let accelerationProgress;
                if (objProgress < 0.3) {
                    // Začátek: pomalá akcelerace (t²)
                    const earlyPhase = objProgress / 0.3;
                    accelerationProgress = earlyPhase * earlyPhase * 0.3;
                } else {
                    // Hlavní fáze: rychlá akcelerace (t² s vyšším koeficientem)
                    const mainPhase = (objProgress - 0.3) / 0.7;
                    accelerationProgress = 0.3 + mainPhase * mainPhase * 0.7;
                }
                
                // Aplikovat rychlostní modifikátor podle výšky (vyšší = pomalejší start)
                const speedMultiplier = obj.speedMultiplier || 1.0;
                // Na začátku je efekt výraznější, později se vyrovnává
                const adjustedProgress = objProgress < 0.5 
                    ? accelerationProgress * (0.5 + speedMultiplier * 0.5) // Pomalejší start pro vyšší
                    : accelerationProgress; // Později se vyrovnává
                
                // Vypočítat směr sklouznutí (dolů a trochu ven)
                const isOnLeft = startPos.x < 0;
                const slideDistance = 10; // Vzdálenost, kterou objekt ujede
                
                // Směr sklouznutí - dolů a ven od středu (s akcelerací a rychlostním modifikátorem)
                const slideY = -slideDistance * adjustedProgress;
                const slideZ = slideDistance * 0.4 * adjustedProgress; // Trochu dopředu
                const slideX = isOnLeft ? -slideDistance * 0.25 * adjustedProgress : slideDistance * 0.25 * adjustedProgress;
                
                // Aktualizovat pozici
                const newPos = new THREE.Vector3(
                    startPos.x + slideX,
                    startPos.y + slideY,
                    startPos.z + slideZ
                );
                
                mesh.position.copy(newPos);
                obj.body.position.set(newPos.x, newPos.y, newPos.z);
                
                // Rotace podle rychlosti (rychlejší rotace při rychlejším pohybu)
                if (!obj.startRot) {
                    obj.startRot = { x: mesh.rotation.x, y: mesh.rotation.y, z: mesh.rotation.z };
                }
                const rotationSpeed = adjustedProgress * 2; // Rotace se zrychluje s pohybem
                mesh.rotation.x = obj.startRot.x + adjustedProgress * 0.8;
                mesh.rotation.y = obj.startRot.y + rotationSpeed * 0.3;
                mesh.rotation.z = obj.startRot.z + adjustedProgress * 0.6;
            }
        });
        
        if (tableProgress < 1 || !allAnimationsDone) {
            requestAnimationFrame(animateTable);
        } else {
            // Animace dokončena - odstranit objekty a zavřít stůl
            objectsToSlide.forEach(obj => {
                if (obj.body) {
                    world.removeBody(obj.body);
                }
                if (obj.mesh) {
                    scene.remove(obj.mesh);
                }
                
                // Odstranit globální reference
                if (obj.isBottle) {
                    bottleBody = null;
                    bottleGroup = null;
                }
                if (obj.isCap) {
                    capBody = null;
                    capMesh = null;
                }
            });
            
            // Odstranit z objectsToUpdate
            objectsToSlide.forEach(obj => {
                if (obj.isPill) {
                    const index = objectsToUpdate.findIndex(o => o.mesh === obj.mesh);
                    if (index !== -1) objectsToUpdate.splice(index, 1);
                }
            });
            
            // Resetovat flagy
            isTableOpening = false;
            tableTiltAngle = 0;
            
            // Po otevření počkat chvíli, pak zavřít
            setTimeout(() => {
                closeTable();
            }, 500);
        }
    }
    
    animateTable();
}

function closeTable() {
    // Animace zavření stolu - obě poloviny se vrátí zpět
    const closeDuration = 1500;
    const startTime = performance.now();
    
    const leftStartRot = tableLeftMesh.rotation.x;
    const rightStartRot = tableRightMesh.rotation.x;
    const targetRot = 0; // Původní rotace (rovně)
    
    function animateTable() {
        const elapsed = performance.now() - startTime;
        const progress = Math.min(elapsed / closeDuration, 1);
        
        const eased = progress < 0.5 
            ? 2 * progress * progress 
            : 1 - Math.pow(-2 * progress + 2, 2) / 2;
        
        // Obě poloviny se vrací zpět
        const currentRot = leftStartRot + eased * (targetRot - leftStartRot);
        tableLeftMesh.rotation.x = currentRot;
        tableRightMesh.rotation.x = rightStartRot + eased * (targetRot - rightStartRot);
        
        // Trackery se automaticky vrací zpět se stolem, protože jsou jeho potomky
        
        // Animace itemů - pohyb se stolem (přilepené)
        objectsToUpdate.forEach(item => {
            if (item.isShopItem && item.tableLocalPos && item.tableHalf) {
                const worldPos = new THREE.Vector3();
                item.tableHalf.localToWorld(worldPos.copy(item.tableLocalPos));
                if (item.mesh) {
                    item.mesh.position.copy(worldPos);
                }
                if (item.body) {
                    item.body.position.set(worldPos.x, worldPos.y, worldPos.z);
                }
            }
        });
        
        if (progress >= 1) {
            // Obnovit fyziku pro itemy
            objectsToUpdate.forEach(item => {
                if (item.isShopItem && item.body) {
                    item.body.type = CANNON.Body.DYNAMIC;
                    item.tableLocalPos = null;
                    item.tableHalf = null;
                }
            });
            // Resetovat flagy
            isTableOpening = false;
            tableTiltAngle = 0;
            // Obnovit obě fyzikální tělesa
            const tableWidth = 10;
            const halfWidth = tableWidth / 2;
            
            // Levá polovina
            const tableShapeLeft = new CANNON.Box(new CANNON.Vec3(halfWidth/2, 5, 3));
            tableLeftBody = new CANNON.Body({
                mass: 0,
                position: new CANNON.Vec3(-halfWidth/2, -5, 0),
                material: world.defaultMaterial
            });
            tableLeftBody.addShape(tableShapeLeft);
            world.addBody(tableLeftBody);
            
            // Pravá polovina
            const tableShapeRight = new CANNON.Box(new CANNON.Vec3(halfWidth/2, 5, 3));
            tableRightBody = new CANNON.Body({
                mass: 0,
                position: new CANNON.Vec3(halfWidth/2, -5, 0),
                material: world.defaultMaterial
            });
            tableRightBody.addShape(tableShapeRight);
            world.addBody(tableRightBody);
            
            // Spawnout novou lahev (bez mince, pokud už není první kolo)
            startNewRound();
        } else {
            requestAnimationFrame(animateTable);
        }
    }
    
    animateTable();
}

function startNewRound() {
    // Odstranit starou lahev a víčko
    if (bottleBody) {
        world.removeBody(bottleBody);
        bottleBody = null;
    }
    if (bottleGroup) {
        scene.remove(bottleGroup);
        bottleGroup = null;
    }
    if (capBody) {
        world.removeBody(capBody);
        capBody = null;
    }
    if (capMesh) {
        scene.remove(capMesh);
        capMesh = null;
    }
    
    // Vyčistit všechny objekty ze scény a fyziky (KROMĚ ITEMŮ)
    const itemsToKeep = [];
    objectsToUpdate.forEach(item => {
        // Neodstraňovat itemy - ty zůstávají
        if (item.isShopItem) {
            itemsToKeep.push(item);
        } else {
            if (item.body) world.removeBody(item.body);
            if (item.mesh) scene.remove(item.mesh);
        }
    });
    // Obnovit objectsToUpdate pouze s itemy
    objectsToUpdate.length = 0;
    objectsToUpdate.push(...itemsToKeep);
    
    // Reset stavu
    isBottleOpen = false;
    isDragging = false;
    draggingObject = null;
    // Toxikace se NERESETUJE - přenáší se mezi koly
    if (mouseConstraint) {
        world.removeConstraint(mouseConstraint);
        if (mouseConstraint.mouseBody) {
            world.removeBody(mouseConstraint.mouseBody);
        }
        mouseConstraint = null;
    }
    
    // Zvýšit číslo kola po každém otevření stolu
    roundNumber++;
    
    // Zobrazit shop před spawnem nové krabičky
    showShop();
}

// Shop systém
const SHOP_ITEMS = ['injector', 'tester', 'pliers', 'tooth', 'candy', 'brain', 'leech', 'hammer', 'hearth'];
let shopSelectedItems = [];
let shopCurrentPlayer = 'player'; // 'player' nebo 'enemy'

function showShop() {
    // Generovat 4 náhodné itemy
    const availableItems = [...SHOP_ITEMS];
    const shopItems = [];
    for (let i = 0; i < 4; i++) {
        const randomIndex = Math.floor(Math.random() * availableItems.length);
        shopItems.push(availableItems[randomIndex]);
        availableItems.splice(randomIndex, 1);
    }
    
    // Resetovat výběr
    shopSelectedItems = [];
    shopCurrentPlayer = 'player';
    
    // Zobrazit shop UI pouze pro hráče
    const shopOverlay = document.getElementById('shop-overlay');
    const shopContainer = document.getElementById('shop-items-container');
    const selectedCount = document.getElementById('shop-selected-count');
    const confirmBtn = document.getElementById('shop-confirm-btn');
    
    shopContainer.innerHTML = '';
    shopSelectedItems = [];
    selectedCount.textContent = '0';
    confirmBtn.style.display = 'none';
    
    // Vytvořit 3D scénu pro shop, pokud ještě neexistuje
    if (!shopScene) {
        initShopScene();
    }
    
    // Vytvořit itemy v shopu s 3D modely
    shopItems.forEach((itemType, index) => {
        const itemDiv = document.createElement('div');
        itemDiv.className = 'shop-item';
        itemDiv.dataset.itemType = itemType;
        itemDiv.style.cssText = `
            width: 200px;
            height: 250px;
            background: rgba(20, 20, 20, 0.5);
            border: 2px solid #444;
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            cursor: pointer;
            font-family: 'Press Start 2P', 'Courier New', monospace;
            font-size: 12px;
            color: white;
            text-align: center;
            padding: 20px;
            box-sizing: border-box;
            transition: all 0.2s;
            position: relative;
            overflow: hidden;
        `;
        
        // Canvas pro 3D model
        const canvas = document.createElement('canvas');
        canvas.width = 200;
        canvas.height = 200;
        canvas.style.cssText = 'width: 100%; height: 200px; pointer-events: none;';
        itemDiv.appendChild(canvas);
        
        // Vytvořit 3D renderer pro tento item
        const itemRenderer = new THREE.WebGLRenderer({ canvas: canvas, alpha: true, antialias: false });
        itemRenderer.setSize(200, 200);
        itemRenderer.setPixelRatio(window.devicePixelRatio);
        
        const itemScene = new THREE.Scene();
        itemScene.background = null;
        
        const itemCamera = new THREE.PerspectiveCamera(45, 200 / 200, 0.1, 100);
        itemCamera.position.set(0, 0, 3);
        itemCamera.lookAt(0, 0, 0);
        
        // Světlo
        const ambientLight = new THREE.AmbientLight(0xffffff, 1.0);
        itemScene.add(ambientLight);
        const dirLight = new THREE.DirectionalLight(0xffffff, 0.8);
        dirLight.position.set(5, 5, 5);
        itemScene.add(dirLight);
        
        // Načíst model pro tento item
        let modelData = null;
        switch(itemType) {
            case 'injector':
                modelData = injectorModelData;
                break;
            case 'tester':
                modelData = testerModelData;
                break;
            case 'pliers':
                modelData = pliersModelData;
                break;
            case 'tooth':
                modelData = toothModelData;
                break;
            case 'candy':
                modelData = candyModelData;
                break;
            case 'brain':
                modelData = brainModelData;
                break;
            case 'leech':
                modelData = leechModelData;
                break;
            case 'hammer':
                modelData = hammerModelData;
                break;
            case 'hearth':
                modelData = hearthModelData;
                break;
        }
        
        let itemModel = null;
        if (modelData && modelData.group) {
            itemModel = modelData.group.clone();
            // Normalizovat velikost
            const box = new THREE.Box3().setFromObject(itemModel);
            const size = box.getSize(new THREE.Vector3());
            const maxDim = Math.max(size.x, size.y, size.z);
            const scale = 1.5 / maxDim;
            itemModel.scale.set(scale, scale, scale);
            itemScene.add(itemModel);
        }
        
        // Animace rotace
        let rotationAngle = 0;
        function animateItem() {
            if (itemModel) {
                rotationAngle += 0.01;
                itemModel.rotation.y = rotationAngle;
            }
            itemRenderer.render(itemScene, itemCamera);
            if (shopOverlay.style.display !== 'none') {
                requestAnimationFrame(animateItem);
            }
        }
        animateItem();
        
        // Uložit renderer a scénu pro cleanup
        itemDiv.shopRenderer = itemRenderer;
        itemDiv.shopScene = itemScene;
        
        itemDiv.addEventListener('click', () => {
            if (shopCurrentPlayer !== 'player') return; // Pouze hráč může klikat
            
            if (shopSelectedItems.includes(index)) {
                // Odznačit
                shopSelectedItems = shopSelectedItems.filter(i => i !== index);
                itemDiv.style.border = '2px solid #444';
                itemDiv.style.background = 'rgba(20, 20, 20, 0.5)';
            } else {
                // Kontrola maximálního počtu itemů
                const currentItemCount = playerItems.length;
                const maxItems = 5;
                const canAdd = maxItems - currentItemCount;
                
                if (shopSelectedItems.length < 2 && shopSelectedItems.length < canAdd) {
                    // Značit (pouze pokud můžeme přidat další itemy)
                    shopSelectedItems.push(index);
                    itemDiv.style.border = '2px solid #0f0';
                    itemDiv.style.background = 'rgba(0, 50, 0, 0.7)';
                }
            }
            
            // Aktualizovat zobrazení
            const currentItemCount = playerItems.length;
            const maxItems = 5;
            const canAdd = maxItems - currentItemCount;
            selectedCount.textContent = `Selected: ${shopSelectedItems.length} / 2 (Items: ${currentItemCount}/${maxItems})`;
            // Zobrazit tlačítko pouze pokud máme 2 vybrané itemy NEBO pokud už máme maximální počet itemů
            const canConfirm = shopSelectedItems.length === 2 || (canAdd > 0 && shopSelectedItems.length === canAdd);
            confirmBtn.style.display = canConfirm ? 'block' : 'none';
        });
        
        shopContainer.appendChild(itemDiv);
    });
    
    shopOverlay.style.display = 'block';
    
    // Event listener pro confirm tlačítko
    confirmBtn.onclick = () => {
        const currentItemCount = playerItems.length;
        const maxItems = 5;
        const canAdd = maxItems - currentItemCount;
        
        // Potvrdit pokud máme 2 vybrané itemy NEBO pokud už máme maximální počet itemů
        if (shopSelectedItems.length > 0 && (shopSelectedItems.length === 2 || shopSelectedItems.length === canAdd)) {
            const selectedTypes = shopSelectedItems.map(i => shopItems[i]);
            handleShopSelection('player', selectedTypes);
            
            // Zavřít shop pro hráče
            shopOverlay.style.display = 'none';
            
            // AI si vybere itemy v pozadí (bez zobrazení shopu)
            setTimeout(() => {
                aiSelectShopItemsSilent(shopItems);
            }, 500);
        }
    };
    
    // Aktualizovat informaci o počtu itemů
    const currentItemCount = playerItems.length;
    const maxItems = 5;
    if (currentItemCount >= maxItems) {
        selectedCount.textContent = `MAX ITEMS (${currentItemCount}/${maxItems})`;
        selectedCount.style.color = '#ff0';
    } else {
        selectedCount.textContent = `Items: ${currentItemCount}/${maxItems}`;
        selectedCount.style.color = 'white';
    }
}

// AI výběr itemů v shopu bez zobrazení UI
function aiSelectShopItemsSilent(shopItems) {
    // Jednoduchá AI strategie: vybrat náhodně 2 itemy
    const selected = [];
    const available = [...Array(shopItems.length).keys()];
    
    for (let i = 0; i < 2; i++) {
        const randomIndex = Math.floor(Math.random() * available.length);
        selected.push(available[randomIndex]);
        available.splice(randomIndex, 1);
    }
    
    const selectedTypes = selected.map(i => shopItems[i]);
    handleShopSelection('enemy', selectedTypes);
    
    // Spawnout novou lahev
    spawnBottle();
    
    // Náhodně rozhodnout, kdo začíná
    const playerStarts = Math.random() > 0.5;
    if (playerStarts) {
        gameState = STATE.PLAYER_TURN;
        startPlayerTurn();
    } else {
        gameState = STATE.ENEMY_TURN;
        startEnemyTurn();
    }
}

function handleShopSelection(owner, itemTypes) {
    // Kontrola maximálního počtu itemů (pouze pro hráče)
    if (owner === 'player') {
        const currentItemCount = playerItems.length;
        const maxItems = 5;
        const canAdd = maxItems - currentItemCount;
        
        if (canAdd <= 0) {
            // Hráč už má maximální počet itemů
            return;
        }
        
        // Přidat pouze tolik itemů, kolik je možné
        const itemsToAdd = Math.min(itemTypes.length, canAdd);
        for (let i = 0; i < itemsToAdd; i++) {
            spawnShopItem(itemTypes[i], owner, i);
        }
    } else {
        // Pro oponenta žádné omezení
        itemTypes.forEach((itemType, index) => {
            spawnShopItem(itemType, owner, index);
        });
    }
}

function spawnShopItem(itemType, owner, itemIndex = 0) {
    let modelData;
    
    switch(itemType) {
        case 'injector':
            modelData = injectorModelData;
            break;
        case 'tester':
            modelData = testerModelData;
            break;
        case 'pliers':
            modelData = pliersModelData;
            break;
        case 'tooth':
            modelData = toothModelData;
            break;
        case 'candy':
            modelData = candyModelData;
            break;
        case 'brain':
            modelData = brainModelData;
            break;
        case 'leech':
            modelData = leechModelData;
            break;
        case 'hammer':
            modelData = hammerModelData;
            break;
        case 'hearth':
            modelData = hearthModelData;
            break;
        default:
            return;
    }
    
    if (!modelData) return;
    
    const { group, boxSize } = modelData;
    const itemGroup = group.clone();
    itemGroup.name = itemType.charAt(0).toUpperCase() + itemType.slice(1) + 'Group';
    scene.add(itemGroup);
    
    // Spawnovat na správných pozicích podle zón na stole
    // Hráč = levý dolní roh (magenta zóna): záporné X, kladné Z (blíže k hráči)
    // Oponent = pravý horní roh (zelená zóna): kladné X, záporné Z (dál od hráče)
    // Rozložit itemy vedle sebe podle jejich pořadí
    // POZOR: Trackery jsou na X=0, Z=2.5 (player) a X=0, Z=-2.5 (enemy) - vyhnout se jim!
    let spawnX, spawnZ;
    const spacing = 0.6; // Rozestup mezi itemy
    const offsetX = itemIndex * spacing; // Offset podle pořadí itemu
    
    if (owner === 'player') {
        // Levý dolní roh - hráčovy itemy (na hráčově straně - levá polovina stolu)
        // Player tracker je na X=0, Z=2.5 - itemy umístit více doleva, aby se vyhnuly trackeru
        const baseX = -2.0; // Začít více vlevo, aby se vyhnuly trackeru na X=0
        spawnX = baseX - offsetX; // Rozložit podél X osy (vedle sebe, směrem doleva)
        spawnZ = 2.5; // Dopředu, blíže k hráči (stejně jako tracker, ale více vlevo)
    } else {
        // Pravý horní roh - oponentovy itemy (na oponentově straně - pravá polovina stolu)
        // Enemy tracker je na X=0, Z=-2.5 - itemy umístit více doprava, aby se vyhnuly trackeru
        const baseX = 2.0; // Začít více vpravo, aby se vyhnuly trackeru na X=0
        spawnX = baseX + offsetX; // Rozložit podél X osy (vedle sebe, směrem doprava)
        spawnZ = -2.5; // Dozadu, dál od hráče (stejně jako tracker, ale více vpravo)
    }
    const spawnY = 5;
    
    // Fyzika
    const itemShape = new CANNON.Box(new CANNON.Vec3(
        boxSize.x / 2,
        boxSize.y / 2,
        boxSize.z / 2
    ));
    
    const itemBody = new CANNON.Body({
        mass: 1,
        position: new CANNON.Vec3(spawnX, spawnY, spawnZ),
        material: world.defaultMaterial,
        linearDamping: 0.5,
        angularDamping: 0.5
    });
    
    itemBody.addShape(itemShape);
    itemBody.userData = { type: itemType, owner: owner, isShopItem: true };
    
    world.addBody(itemBody);
    objectsToUpdate.push({ 
        mesh: itemGroup, 
        body: itemBody, 
        isShopItem: true,
        owner: owner,
        itemType: itemType
    });
    
    // Nastavit globální proměnné pro tento typ itemu (pouze pokud je první instance)
    if (owner === 'player') {
        if (itemType === 'injector' && !injectorBody) {
            injectorGroup = itemGroup;
            injectorBody = itemBody;
        } else if (itemType === 'tester' && !testerBody) {
            testerGroup = itemGroup;
            testerBody = itemBody;
        } else if (itemType === 'pliers' && !pliersBody) {
            pliersGroup = itemGroup;
            pliersBody = itemBody;
        } else if (itemType === 'tooth' && !toothBody) {
            toothGroup = itemGroup;
            toothBody = itemBody;
        } else if (itemType === 'candy' && !candyBody) {
            candyGroup = itemGroup;
            candyBody = itemBody;
        } else if (itemType === 'brain' && !brainBody) {
            brainGroup = itemGroup;
            brainBody = itemBody;
        } else if (itemType === 'leech' && !leechBody) {
            leechGroup = itemGroup;
            leechBody = itemBody;
        } else if (itemType === 'hammer' && !hammerBody) {
            hammerGroup = itemGroup;
            hammerBody = itemBody;
        } else if (itemType === 'hearth' && !hearthBody) {
            hearthGroup = itemGroup;
            hearthBody = itemBody;
        }
        playerItems.push({ type: itemType, mesh: itemGroup, body: itemBody, owner: 'player' });
    } else {
        enemyItems.push({ type: itemType, mesh: itemGroup, body: itemBody, owner: 'enemy' });
    }
}

function initShopScene() {
    // Shop scéna se inicializuje při prvním použití
    // Používáme jednotlivé renderery pro každý item
}


// AI logika pro použití itemů
function aiUseItems() {
    // Najít itemy oponenta
    const enemyItemObjects = objectsToUpdate.filter(o => o.isShopItem && o.owner === 'enemy');
    
    if (enemyItemObjects.length === 0) return;
    
    // Jednoduchá strategie: použít náhodný item s určitou pravděpodobností
    const useChance = 0.3; // 30% šance použít item v každém tahu
    
    if (Math.random() < useChance) {
        const randomItem = enemyItemObjects[Math.floor(Math.random() * enemyItemObjects.length)];
        const itemType = randomItem.itemType;
        
        // Nastavit globální proměnné podle typu
        switch(itemType) {
            case 'injector':
                injectorGroup = randomItem.mesh;
                injectorBody = randomItem.body;
                useInjector();
                break;
            case 'tester':
                testerGroup = randomItem.mesh;
                testerBody = randomItem.body;
                useTester();
                break;
            case 'pliers':
                pliersGroup = randomItem.mesh;
                pliersBody = randomItem.body;
                usePliers();
                break;
            case 'tooth':
                toothGroup = randomItem.mesh;
                toothBody = randomItem.body;
                useTooth();
                break;
            case 'candy':
                candyGroup = randomItem.mesh;
                candyBody = randomItem.body;
                useCandy();
                break;
            case 'brain':
                brainGroup = randomItem.mesh;
                brainBody = randomItem.body;
                useBrain();
                break;
        }
    }
}

// AI logika pro drag itemů do rohu
function aiOrganizeItems() {
    // Organizovat itemy oponenta do pravého horního rohu (zelená zóna) na oponentově straně stolu
    // POZOR: Enemy tracker je na X=0, Z=-2.5 - itemy umístit více doprava, aby se vyhnuly trackeru
    // Pozice: X = 2.0+ (pravá strana stolu, vyhnout se trackeru na X=0), Z = -2.5 (dozadu, dál od hráče), Y = 0.5 (na stole)
    const baseX = 2.0; // Začít více vpravo, aby se vyhnuly trackeru na X=0
    const targetZ = -2.5;
    const targetY = 0.5;
    
    const enemyItemObjects = objectsToUpdate.filter(o => o.isShopItem && o.owner === 'enemy' && o.body);
    
    enemyItemObjects.forEach((item, index) => {
        // Rozložit itemy v řadě podél X osy (vedle sebe)
        const spacing = 0.6; // Rozestup mezi itemy
        const offsetX = index * spacing;
        const finalX = baseX + offsetX; // Rozložit doprava od baseX
        const finalZ = targetZ;
        
        // Animovat item na pozici
        if (item.body && item.mesh) {
            item.body.type = CANNON.Body.KINEMATIC;
            item.body.velocity.set(0, 0, 0);
            item.body.angularVelocity.set(0, 0, 0);
            
            // Plynulá animace
            const startPos = item.mesh.position.clone();
            const targetPos = new THREE.Vector3(finalX, targetY, finalZ);
            const duration = 1000;
            const startTime = performance.now();
            
            function animateMove() {
                const elapsed = performance.now() - startTime;
                const progress = Math.min(elapsed / duration, 1);
                const eased = progress < 0.5 
                    ? 2 * progress * progress 
                    : 1 - Math.pow(-2 * progress + 2, 2) / 2;
                
                const currentPos = startPos.clone().lerp(targetPos, eased);
                item.mesh.position.copy(currentPos);
                item.body.position.set(currentPos.x, currentPos.y, currentPos.z);
                
                if (progress < 1) {
                    requestAnimationFrame(animateMove);
                } else {
                    item.body.type = CANNON.Body.DYNAMIC;
                }
            }
            
            animateMove();
        }
    });
}

function checkGameOver() {
    if (playerHP <= 0) {
        gameState = STATE.GAME_OVER;
        showStatus("ZEMŘEL JSI. KONEC HRY.", true);
    } else if (enemyHP <= 0) {
        gameState = STATE.GAME_OVER;
        showStatus("VYHRÁL JSI!", true);
    }
}

function updateUI() {
    // Aktualizovat tracker textury místo HTML elementů
    
    // Tracker pro hráče (funguje i bez trackerBaseTexture)
    if (playerTrackerMesh) {
        playerTrackerTexture = createTrackerTexture(trackerBaseTexture, playerHP, playerToxicity, true);
        playerTrackerMesh.material.map = playerTrackerTexture;
        playerTrackerMesh.material.needsUpdate = true;
    }
    
    // Tracker pro oponenta (funguje i bez trackerBaseTexture)
    if (enemyTrackerMesh) {
        enemyTrackerTexture = createTrackerTexture(trackerBaseTexture, enemyHP, enemyToxicity, false);
        enemyTrackerMesh.material.map = enemyTrackerTexture;
        enemyTrackerMesh.material.needsUpdate = true;
    }
    
    // Staré HTML elementy (ponechat pro kompatibilitu, ale skryté)
    if (uiPlayerHP) uiPlayerHP.style.display = 'none';
    if (uiEnemyHP) uiEnemyHP.style.display = 'none';
    if (uiPlayerToxicity) uiPlayerToxicity.style.display = 'none';
    if (uiEnemyToxicity) uiEnemyToxicity.style.display = 'none';
}

function updatePillStatsUI() {
    if (!uiPillStats) return;
    
    // Použít fixní seznam všech pilulek spawnnutých v kole (ne aktuální na stole)
    const pills = currentRoundPills;
    
    // Statistiky podle typu
    const stats = {
        normal: { total: 0, poison: 0, good: 0 },
        pillTablet: { total: 0, poison: 0, reducesToxicity: 0 },
        vitaminPill: { total: 0, poison: 0, addsToxicity: 0 }
    };
    
    pills.forEach(pill => {
        if (pill.isPillTablet) {
            stats.pillTablet.total++;
            if (pill.isPoison) {
                stats.pillTablet.poison++;
            } else if (pill.reducesToxicity) {
                stats.pillTablet.reducesToxicity++;
            }
        } else if (pill.isVitaminPill) {
            stats.vitaminPill.total++;
            if (pill.isPoison) {
                stats.vitaminPill.poison++;
            } else if (pill.addsToxicity) {
                stats.vitaminPill.addsToxicity++;
            }
        } else {
            stats.normal.total++;
            if (pill.isPoison) {
                stats.normal.poison++;
            } else {
                stats.normal.good++;
            }
        }
    });
    
    // Vytvořit HTML
    let html = '<div style="font-size: 10px; margin-bottom: 10px; border-bottom: 2px solid #444; padding-bottom: 8px;">PILULKY V KOLE:</div>';
    
    // Normální pilulky - jeden řádek s všemi efekty
    if (stats.normal.total > 0) {
        const effects = [];
        if (stats.normal.good > 0) {
            effects.push(`<span class="pill-stat-icon">💊</span> +1 toxikace`);
        }
        if (stats.normal.poison > 0) {
            effects.push(`<span class="pill-stat-icon">💀</span> smrt`);
        }
        html += `<div class="pill-stat-item"><span>${stats.normal.total}x</span><span>(${effects.join(', ')})</span></div>`;
    }
    
    // Pilltablet - jeden řádek s všemi efekty
    if (stats.pillTablet.total > 0) {
        const effects = [];
        if (stats.pillTablet.reducesToxicity > 0) {
            effects.push(`<span class="pill-stat-icon">🔷</span> -2 toxikace`);
        }
        if (stats.pillTablet.poison > 0) {
            effects.push(`<span class="pill-stat-icon">💀</span> smrt`);
        }
        html += `<div class="pill-stat-item"><span>${stats.pillTablet.total}x</span><span>(${effects.join(', ')})</span></div>`;
    }
    
    // Vitamin pills - jeden řádek s všemi efekty
    if (stats.vitaminPill.total > 0) {
        const effects = [];
        if (stats.vitaminPill.addsToxicity > 0) {
            effects.push(`<span class="pill-stat-icon">💚</span> +2 toxikace`);
        }
        if (stats.vitaminPill.poison > 0) {
            effects.push(`<span class="pill-stat-icon">💀</span> smrt`);
        }
        html += `<div class="pill-stat-item"><span>${stats.vitaminPill.total}x</span><span>(${effects.join(', ')})</span></div>`;
    }
    
    if (pills.length === 0) {
        html = '<div style="color: #888; font-size: 10px;">ZADNE PILULKY</div>';
    }
    
    uiPillStats.innerHTML = html;
}

function showStatus(text, visible) {
    uiStatus.innerText = text;
    uiStatus.style.display = visible ? 'block' : 'none';
}

function onWindowResize() {
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    // PS1 HORROR STYL: Udržet low resolution rendering (50% rozlišení)
    const ps1Scale = 0.5;
    renderer.setSize(window.innerWidth * ps1Scale, window.innerHeight * ps1Scale, false);
}

function animate() {
    requestAnimationFrame(animate);
    const time = performance.now() / 1000;
    if (!lastCallTime) lastCallTime = time;
    const dt = time - lastCallTime;
    lastCallTime = time;

    // Aktualizovat zombie animace, pokud existují
    if (zombieMixer) {
        zombieMixer.update(dt);
    }

    world.step(timeStep, dt, 10); 
    
    // SMOOTH DRAG (Plynulý pohyb myši + Zvedání jen pro lahev)
    if (isDragging && mouseConstraint && mouseConstraint.mouseBody) {
         const lerpFactor = 0.15; 
         const currentPos = mouseConstraint.mouseBody.position;
         
         if (draggingObject === 'bottle') {
             // Pro lahev: zvedání a rotace
             const targetLift = 2.5;
             currentLift += (targetLift - currentLift) * 0.05; 
             
             // X a Z sledují myš
             currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
             currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
             
             // Y sleduje myš + offset
             const targetY = mouseTargetPos.y + currentLift;
             currentPos.y += (targetY - currentPos.y) * lerpFactor;
             
             // ABSOLUTNÍ LIMIT VÝŠKY (Strop)
             if (currentPos.y > 3.5) currentPos.y = 3.5;
         } else if (draggingObject === 'cap') {
             // Pro víčko: jen sledování myši (bez zvedání)
             currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
             currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
             currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'pill' && potentialPillBody) {
            // Pro pilulku: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'injector' && injectorBody) {
            // Pro injector: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'tester' && testerBody) {
            // Pro tester: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'pliers' && pliersBody) {
            // Pro kleště: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'tooth' && toothBody) {
            // Pro zub: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'candy' && candyBody) {
            // Pro candy: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'brain' && brainBody) {
            // Pro brain: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'leech' && leechBody) {
            // Pro leech: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'hammer' && hammerBody) {
            // Pro hammer: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        } else if (draggingObject === 'hearth' && hearthBody) {
            // Pro hearth: sledování myši (podobně jako víčko)
            currentPos.x += (mouseTargetPos.x - currentPos.x) * lerpFactor;
            currentPos.y += (mouseTargetPos.y - currentPos.y) * lerpFactor;
            currentPos.z += (mouseTargetPos.z - currentPos.z) * lerpFactor;
        }
    }

    
    // Stabilizace lahve při držení - gravitace kolmo dolů, hrdlem dolů
    if (isDragging && draggingObject === 'bottle' && bottleBody) {
        // Silně tlumíme rotaci, aby lahev byla stabilní
        bottleBody.angularVelocity.x *= 0.8;
        bottleBody.angularVelocity.y *= 0.8;
        bottleBody.angularVelocity.z *= 0.8;
        
        // Zajistíme, aby lahev byla kolmo hrdlem dolů (hrdlo = -Y, dno = +Y)
        const currentUp = new CANNON.Vec3(0, 1, 0);
        bottleBody.quaternion.vmult(currentUp, currentUp);
        
        // Cílová orientace: hrdlo dolů (Y = -1, takže up vektor je -1)
        const targetUp = new CANNON.Vec3(0, -1, 0);
        const axis = new CANNON.Vec3();
        currentUp.cross(targetUp, axis);
        
        const dot = currentUp.dot(targetUp);
        const angle = Math.acos(Math.max(-1, Math.min(1, dot)));
        
        // Pokud lahev není hrdlem dolů, pomalu ji narovnáme
        if (angle > 0.1 && axis.length() > 0.001) {
            const correctionSpeed = 2.0; // Rychlost korekce
            axis.unit();
            axis.scale(angle * correctionSpeed, axis);
            bottleBody.angularVelocity.vadd(axis, bottleBody.angularVelocity);
        }
    }

    // Animace preview mince
    if (gameState === STATE.WAITING_FOR_TOSS && previewCoinMesh) {
        previewCoinMesh.rotation.y += dt; 
        previewCoinMesh.rotation.x = Math.PI/2 + Math.sin(time * 2) * 0.2; 
        previewCoinMesh.position.y = 0.5 + Math.sin(time * 1.5) * 0.1; // Nízko nad stolem
    }

    // Logika mince
    if (gameState === STATE.COIN_FLYING && coinBody) {
        // Záchranná síť
        if (coinBody.position.y < -0.5) {
            coinBody.position.set(0, 0.2, 0); 
            coinBody.velocity.set(0, 0, 0);
            coinBody.angularVelocity.set(0, 0, 0);
            coinBody.quaternion.setFromAxisAngle(new CANNON.Vec3(1,0,0), 0);
        }

        // Zastavení -> přechod do COIN_LANDED
        if (coinBody.velocity.length() < 0.05 && coinBody.angularVelocity.length() < 0.1 && coinBody.position.y < 0.3) {
            
            const meshUp = new THREE.Vector3(0, 1, 0);
            meshUp.applyQuaternion(coinMesh.quaternion);
            
            // Silná kontrola hrany - pokud je mince blízko hraně, donutíme ji spadnout na jednu stranu
            if (Math.abs(meshUp.y) < 0.7) {
                // Mince je blízko hraně - aplikujeme silný točivý moment, aby spadla
                const force = meshUp.y > 0 ? 5 : -5; // Tlačíme na stranu, která je více nahoře
                coinBody.angularVelocity.set(force * 2, 0, 0); 
                // Dáme také trochu rychlosti dolů, aby mince pokračovala v pohybu
                coinBody.velocity.set(0, -0.1, 0);
                return; 
            }

            // Zastaveno! Přejdeme do stavu, kdy čekáme na klik.
            // Ještě jednou zkontrolujeme, že mince není na hraně
            if (Math.abs(meshUp.y) < 0.8) {
                // Pokud je stále blízko hraně, donutíme ji definitivně spadnout
                const force = meshUp.y > 0 ? 10 : -10;
                coinBody.angularVelocity.set(force, 0, 0);
                coinBody.velocity.set(0, -0.2, 0);
                coinBody.type = CANNON.Body.DYNAMIC; // Ujistíme se, že je dynamická
                return;
            }

            gameState = STATE.COIN_LANDED;
            
            // Zjistíme vítěze, ale zatím nespustíme hru
            const playerStarts = meshUp.y > 0;
            coinMesh.userData.playerStarts = playerStarts; // Uložíme výsledek
            
            // Zastavíme fyziku mince úplně, aby se nehýbala
            coinBody.type = CANNON.Body.STATIC;
        }
    }

    for (const obj of objectsToUpdate) {
        obj.mesh.position.copy(obj.body.position);
        obj.mesh.quaternion.copy(obj.body.quaternion);
    }
    
    // Aktualizovat zombie podle debug hodnot
    if (zombieGroup) {
        zombieGroup.position.set(zombieDebugPos.x, zombieDebugPos.y, zombieDebugPos.z);
        zombieGroup.rotation.set(zombieDebugRot.x, zombieDebugRot.y, zombieDebugRot.z);
        zombieGroup.scale.set(zombieDebugScale, zombieDebugScale, zombieDebugScale);
        
        // PS1 HORROR STYL: Wobble efekt pro zombie (vratké vertex wobble)
        zombieGroup.traverse((child) => {
            if (child.isMesh && child.geometry) {
                applyWobbleEffect(child, 0.03); // Wobble intenzita pro hororový efekt
            }
        });
    }
    
    // Aplikovat debug rotaci stolu, pokud je debug mód aktivní a stůl se neotáčí
    if (isDebugMode && !isTableOpening) {
        if (tableLeftMesh) {
            tableLeftMesh.rotation.x = tableDebugRotationX;
            // Ujistit se, že materiál stolu má správné nastavení pro viditelnost
            if (tableLeftMesh.material) {
                tableLeftMesh.material.depthTest = true; // Vždy zapnout depth test, aby zakryl zombie
                tableLeftMesh.material.depthWrite = true;
                tableLeftMesh.material.needsUpdate = true;
            }
        }
        if (tableRightMesh) {
            tableRightMesh.rotation.x = tableDebugRotationX;
            // Ujistit se, že materiál stolu má správné nastavení pro viditelnost
            if (tableRightMesh.material) {
                tableRightMesh.material.depthTest = true; // Vždy zapnout depth test, aby zakryl zombie
                tableRightMesh.material.depthWrite = true;
                tableRightMesh.material.needsUpdate = true;
            }
        }
        
        // Upravit trackery, aby byly vždy viditelné, i když je stůl nakloněný
        if (Math.abs(tableDebugRotationX) > 0.18) {
            // Pokud je stůl nakloněný, zajistit, aby trackery byly vždy viditelné
            if (playerTrackerMesh && playerTrackerMesh.material) {
                playerTrackerMesh.material.depthTest = false; // Vypnout depth test, aby se tracker vždy renderoval
                playerTrackerMesh.material.depthWrite = true;
                playerTrackerMesh.material.needsUpdate = true;
            }
            if (enemyTrackerMesh && enemyTrackerMesh.material) {
                enemyTrackerMesh.material.depthTest = false; // Vypnout depth test, aby se tracker vždy renderoval
                enemyTrackerMesh.material.depthWrite = true;
                enemyTrackerMesh.material.needsUpdate = true;
            }
        } else {
            // Pokud je stůl normální, použít normální depth test
            if (playerTrackerMesh && playerTrackerMesh.material) {
                playerTrackerMesh.material.depthTest = true;
                playerTrackerMesh.material.depthWrite = true;
                playerTrackerMesh.material.needsUpdate = true;
            }
            if (enemyTrackerMesh && enemyTrackerMesh.material) {
                enemyTrackerMesh.material.depthTest = true;
                enemyTrackerMesh.material.depthWrite = true;
                enemyTrackerMesh.material.needsUpdate = true;
            }
        }
    }
    
    // PS1 HORROR STYL: Wobble efekt pro stůl (jemnější) - pouze pokud není debug mód nebo animace
    if (!isDebugMode || isTableOpening) {
        if (tableLeftMesh && tableLeftMesh.userData.isPS1Table) {
            applyWobbleEffect(tableLeftMesh, 0.0001); // Jemnější wobble pro stůl
        }
        if (tableRightMesh && tableRightMesh.userData.isPS1Table) {
            applyWobbleEffect(tableRightMesh, 0.0001);
        }
    }
    
    renderer.render(scene, camera);
}

// Debug mód pro zombie
function initDebugMode() {
    const debugToggle = document.getElementById('debug-toggle');
    const debugPanel = document.getElementById('debug-panel');
    
    if (!debugToggle || !debugPanel) return; // UI ještě není načteno
    
    // Tlačítko pro zapnutí/vypnutí debug módu
    debugToggle.addEventListener('click', () => {
        isDebugMode = !isDebugMode;
        debugPanel.classList.toggle('active', isDebugMode);
        debugToggle.textContent = isDebugMode ? 'DEBUG (ON)' : 'DEBUG';
        debugToggle.style.background = isDebugMode ? 'rgba(200, 0, 0, 0.8)' : 'rgba(0, 150, 0, 0.8)';
    });
    
    // Posuvníky pro pozici
    const posXSlider = document.getElementById('debug-pos-x');
    const posYSlider = document.getElementById('debug-pos-y');
    const posZSlider = document.getElementById('debug-pos-z');
    const posXVal = document.getElementById('debug-pos-x-val');
    const posYVal = document.getElementById('debug-pos-y-val');
    const posZVal = document.getElementById('debug-pos-z-val');
    
    if (posXSlider && posXVal) {
        posXSlider.addEventListener('input', (e) => {
            zombieDebugPos.x = parseFloat(e.target.value);
            posXVal.textContent = zombieDebugPos.x.toFixed(2);
        });
    }
    
    if (posYSlider && posYVal) {
        posYSlider.addEventListener('input', (e) => {
            zombieDebugPos.y = parseFloat(e.target.value);
            posYVal.textContent = zombieDebugPos.y.toFixed(2);
        });
    }
    
    if (posZSlider && posZVal) {
        posZSlider.addEventListener('input', (e) => {
            zombieDebugPos.z = parseFloat(e.target.value);
            posZVal.textContent = zombieDebugPos.z.toFixed(2);
        });
    }
    
    // Posuvníky pro rotaci X, Y, Z
    const rotXSlider = document.getElementById('debug-rot-x');
    const rotXVal = document.getElementById('debug-rot-x-val');
    
    if (rotXSlider && rotXVal) {
        rotXSlider.addEventListener('input', (e) => {
            zombieDebugRot.x = parseFloat(e.target.value);
            rotXVal.textContent = zombieDebugRot.x.toFixed(2);
        });
    }
    
    const rotYSlider = document.getElementById('debug-rot-y');
    const rotYVal = document.getElementById('debug-rot-y-val');
    
    if (rotYSlider && rotYVal) {
        rotYSlider.addEventListener('input', (e) => {
            zombieDebugRot.y = parseFloat(e.target.value);
            rotYVal.textContent = zombieDebugRot.y.toFixed(2);
        });
    }
    
    const rotZSlider = document.getElementById('debug-rot-z');
    const rotZVal = document.getElementById('debug-rot-z-val');
    
    if (rotZSlider && rotZVal) {
        rotZSlider.addEventListener('input', (e) => {
            zombieDebugRot.z = parseFloat(e.target.value);
            rotZVal.textContent = zombieDebugRot.z.toFixed(2);
        });
    }
    
    // Posuvník pro měřítko zombie
    const scaleSlider = document.getElementById('debug-scale');
    const scaleVal = document.getElementById('debug-scale-val');
    
    if (scaleSlider && scaleVal) {
        scaleSlider.addEventListener('input', (e) => {
            zombieDebugScale = parseFloat(e.target.value);
            scaleVal.textContent = zombieDebugScale.toFixed(2);
        });
    }
    
    // Posuvník pro výšku úst oponenta
    const enemyMouthHeightSlider = document.getElementById('debug-enemy-mouth-height');
    const enemyMouthHeightVal = document.getElementById('debug-enemy-mouth-height-val');
    
    if (enemyMouthHeightSlider && enemyMouthHeightVal) {
        enemyMouthHeightSlider.addEventListener('input', (e) => {
            enemyMouthHeight = parseFloat(e.target.value);
            enemyMouthHeightVal.textContent = enemyMouthHeight.toFixed(2);
        });
    }
    
    // Posuvník pro měřítko krabičky a víčka
    const bottleCapScaleSlider = document.getElementById('debug-bottle-cap-scale');
    const bottleCapScaleVal = document.getElementById('debug-bottle-cap-scale-val');
    
    if (bottleCapScaleSlider && bottleCapScaleVal) {
        bottleCapScaleSlider.addEventListener('input', (e) => {
            bottleCapScale = parseFloat(e.target.value);
            bottleCapScaleVal.textContent = bottleCapScale.toFixed(2);
            // Aktualizovat lahev, pokud už existuje
            if (bottleModelData) {
                // Znovu načíst lahev s novým měřítkem
                const loader = new FBXLoader();
                loader.load('models/Simple Pill Bottle/Bottle.fbx', (obj) => {
                    try {
                        const { group, boxSize } = normalizeAndCenterModel(obj, bottleCapScale);
                        group.name = "BottleGroup";
                        bottleModelData = { group, boxSize };
                    } catch (err) {
                        console.error('Chyba při přenačítání lahve:', err);
                    }
                });
            }
        });
    }
    
    // Posuvník pro překlopení stolu (rotace X)
    const tableRotationXSlider = document.getElementById('debug-table-rotation-x');
    const tableRotationXVal = document.getElementById('debug-table-rotation-x-val');
    
    if (tableRotationXSlider && tableRotationXVal) {
        tableRotationXSlider.addEventListener('input', (e) => {
            tableDebugRotationX = parseFloat(e.target.value);
            tableRotationXVal.textContent = tableDebugRotationX.toFixed(2);
            // Okamžitě aplikovat rotaci na stůl
            if (tableLeftMesh) {
                tableLeftMesh.rotation.x = tableDebugRotationX;
            }
            if (tableRightMesh) {
                tableRightMesh.rotation.x = tableDebugRotationX;
            }
        });
    }
    
    // Tlačítko pro kopírování hodnot
    const copyBtn = document.getElementById('debug-copy');
    if (copyBtn) {
        copyBtn.addEventListener('click', () => {
            const values = `position: { x: ${zombieDebugPos.x.toFixed(3)}, y: ${zombieDebugPos.y.toFixed(3)}, z: ${zombieDebugPos.z.toFixed(3)} },
rotation: { x: ${zombieDebugRot.x.toFixed(3)}, y: ${zombieDebugRot.y.toFixed(3)}, z: ${zombieDebugRot.z.toFixed(3)} },
scale: ${zombieDebugScale.toFixed(3)},
enemyMouthHeight: ${enemyMouthHeight.toFixed(3)},
bottleCapScale: ${bottleCapScale.toFixed(3)},
tableRotationX: ${tableDebugRotationX.toFixed(3)}`;
            
            navigator.clipboard.writeText(values).then(() => {
                copyBtn.textContent = 'Zkopírováno!';
                setTimeout(() => {
                    copyBtn.textContent = 'Kopírovat hodnoty';
                }, 2000);
            }).catch(() => {
                // Fallback pro starší prohlížeče
                const textarea = document.createElement('textarea');
                textarea.value = values;
                document.body.appendChild(textarea);
                textarea.select();
                document.execCommand('copy');
                document.body.removeChild(textarea);
                copyBtn.textContent = 'Zkopírováno!';
                setTimeout(() => {
                    copyBtn.textContent = 'Kopírovat hodnoty';
                }, 2000);
            });
        });
    }
}
