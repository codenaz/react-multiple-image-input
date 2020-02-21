# React Multple Image Upload

![demo](https://s5.gifyu.com/images/upload-demo.gif)

A library for adding a simple multiple image upload and cropping feature to your react app.

Requires react >= 16.8.0

This package makes use of [react-image-cropper](https://github.com/DominicTobias/react-image-crop)

## Installation

Run the following command:
`npm install react-multiple-image-upload`

## Usage

```javascript
import React, { useState } from 'react';
import MultiImageInput from 'react-multiple-image-uploader';

function App() {
  const crop = {
    unit: '%',
    aspect: 4 / 3,
    width: '100'
  };

  const [images, setImages] = useState({});

  return (
    <MultiImageInput
      images={setImages}
      setImages={setImages}
      cropConfig={{ crop }}
    />
  );
}

export default App;
```

## Props

| Property   | Type                | Default | Description                                                                                       |
| ---------- | ------------------- | ------- | ------------------------------------------------------------------------------------------------- |
| images     | Object (required)   |         | A state variable for holding the images                                                           |
| setImages  | function (required) |         | A function that updates the images state                                                          |
| max        | number              | `3`     | Max number of images allowed                                                                      |
| allowCrop  | bool                | `true`  | Set to false to disable cropping                                                                  |
| cropConfig | Object              |         | specifies cropping dimensions and limits                                                          | refer to https://github.com/DominicTobias/react-image-crop#props |
| theme      | Object or String    | `dark`  | Can be a simple string that specifies light or dark, or an object with your custom configurations |

## Props Explained

```

```
