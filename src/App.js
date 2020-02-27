import React, { useState } from 'react';
// import MultiImageInput from './lib/multi-image-input';
import MultiImageInput from 'react-multiple-image-input';

function App() {
  const crop = {
    unit: '%',
    aspect: 4 / 3,
    width: '100'
  };

  const [images, setImages] = useState({});

  return (
    <div className="App" style={{ maxWidth: '36rem' }}>
      <header className="App-header">
        <MultiImageInput
          images={images}
          setImages={setImages}
          cropConfig={{ crop, ruleOfThirds: true, minWidth: 300 }}
        />
      </header>
    </div>
  );
}

export default App;
